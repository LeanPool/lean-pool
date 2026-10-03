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
    (nb078_alpha_dummy_569) ∈
      (((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_577) from (by
          unfold nb078_alpha_dummy_577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_578) from (by
            unfold nb078_alpha_dummy_578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0597 (g : Var) :
    (nb078_alpha_dummy_572 g) ∈
      (((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_579 g) from (by
          unfold nb078_alpha_dummy_579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_580 g) from (by
            unfold nb078_alpha_dummy_580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0598 :
    (nb078_alpha_dummy_578) ∈ (((Class.cv (nb078_alpha_dummy_578))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0599 (g : Var) :
    (nb078_alpha_dummy_580 g) ∈ (((Class.cv (nb078_alpha_dummy_580 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0600 :
    (nb078_alpha_dummy_585) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_585))).fv) :=
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
    (nb078_alpha_dummy_587 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_587 g))).fv) :=
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
    (nb078_alpha_dummy_585) ∈
      (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0603 (g : Var) :
    (nb078_alpha_dummy_587 g) ∈
      (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0604 :
    (nb078_alpha_dummy_592) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_592))
            (Class.cv (nb078_alpha_dummy_593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0605 (g : Var) :
    (nb078_alpha_dummy_595 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0606 :
    (nb078_alpha_dummy_592) ∈
      (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0607 (g : Var) :
    (nb078_alpha_dummy_595 g) ∈
      (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0608 :
    (nb078_alpha_dummy_593) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_592))
            (Class.cv (nb078_alpha_dummy_593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0609 (g : Var) :
    (nb078_alpha_dummy_596 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g))
            (Class.cv (nb078_alpha_dummy_596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0610 :
    (nb078_alpha_dummy_593) ∈
      (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0611 (g : Var) :
    (nb078_alpha_dummy_596 g) ∈
      (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0612 :
    (nb078_alpha_dummy_592) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0613 (g : Var) :
    (nb078_alpha_dummy_595 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0614 :
    (nb078_alpha_dummy_592) ∈
      (((Class.cv (nb078_alpha_dummy_592))).fv ∪ ((Class.cv (nb078_alpha_dummy_592))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0615 (g : Var) :
    (nb078_alpha_dummy_595 g) ∈
      (((Class.cv (nb078_alpha_dummy_595 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_595 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0616 :
    (nb078_alpha_dummy_593) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_592)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_593)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0617 (g : Var) :
    (nb078_alpha_dummy_596 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_595 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_596 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0618 :
    (nb078_alpha_dummy_593) ∈
      (((Class.cv (nb078_alpha_dummy_593))).fv ∪ ((Class.cv (nb078_alpha_dummy_593))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0619 (g : Var) :
    (nb078_alpha_dummy_596 g) ∈
      (((Class.cv (nb078_alpha_dummy_596 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_596 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0620 :
    (nb078_alpha_dummy_570) ∈
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0621 :
    (nb078_alpha_dummy_570) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_577) from (by
          unfold nb078_alpha_dummy_577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_578) from (by
            unfold nb078_alpha_dummy_578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0622 (g : Var) :
    (nb078_alpha_dummy_573 g) ∈
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0623 (g : Var) :
    (nb078_alpha_dummy_573 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_579 g) from (by
          unfold nb078_alpha_dummy_579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_580 g) from (by
            unfold nb078_alpha_dummy_580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0624 :
    (nb078_alpha_dummy_570) ∈
      (((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_577) from (by
          unfold nb078_alpha_dummy_577;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_578) from (by
            unfold nb078_alpha_dummy_578;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0625 (g : Var) :
    (nb078_alpha_dummy_573 g) ∈
      (((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_579 g) from (by
          unfold nb078_alpha_dummy_579;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_580 g) from (by
            unfold nb078_alpha_dummy_580;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0626 :
    (nb078_alpha_dummy_578) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0627 (g : Var) :
    (nb078_alpha_dummy_580 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0628 :
    (nb078_alpha_dummy_578) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0629 (g : Var) :
    (nb078_alpha_dummy_580 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0630 :
    (nb078_alpha_dummy_569) ∈
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0631 :
    (nb078_alpha_dummy_569) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_613) from (by
          unfold nb078_alpha_dummy_613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_614) from (by
            unfold nb078_alpha_dummy_614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0632 (g : Var) :
    (nb078_alpha_dummy_572 g) ∈
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0633 (g : Var) :
    (nb078_alpha_dummy_572 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_615 g) from (by
          unfold nb078_alpha_dummy_615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_616 g) from (by
            unfold nb078_alpha_dummy_616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0634 :
    (nb078_alpha_dummy_569) ∈
      (((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_613) from (by
          unfold nb078_alpha_dummy_613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_614) from (by
            unfold nb078_alpha_dummy_614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0635 (g : Var) :
    (nb078_alpha_dummy_572 g) ∈
      (((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_615 g) from (by
          unfold nb078_alpha_dummy_615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_616 g) from (by
            unfold nb078_alpha_dummy_616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0636 :
    (nb078_alpha_dummy_614) ∈ (((Class.cv (nb078_alpha_dummy_614))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0637 (g : Var) :
    (nb078_alpha_dummy_616 g) ∈ (((Class.cv (nb078_alpha_dummy_616 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0638 :
    (nb078_alpha_dummy_621) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_621))).fv) :=
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
    (nb078_alpha_dummy_623 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_623 g))).fv) :=
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
    (nb078_alpha_dummy_621) ∈
      (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0641 (g : Var) :
    (nb078_alpha_dummy_623 g) ∈
      (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0642 :
    (nb078_alpha_dummy_628) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_628))
            (Class.cv (nb078_alpha_dummy_629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0643 (g : Var) :
    (nb078_alpha_dummy_631 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0644 :
    (nb078_alpha_dummy_628) ∈
      (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0645 (g : Var) :
    (nb078_alpha_dummy_631 g) ∈
      (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0646 :
    (nb078_alpha_dummy_629) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_628))
            (Class.cv (nb078_alpha_dummy_629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0647 (g : Var) :
    (nb078_alpha_dummy_632 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g))
            (Class.cv (nb078_alpha_dummy_632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0648 :
    (nb078_alpha_dummy_629) ∈
      (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0649 (g : Var) :
    (nb078_alpha_dummy_632 g) ∈
      (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0650 :
    (nb078_alpha_dummy_628) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0651 (g : Var) :
    (nb078_alpha_dummy_631 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0652 :
    (nb078_alpha_dummy_628) ∈
      (((Class.cv (nb078_alpha_dummy_628))).fv ∪ ((Class.cv (nb078_alpha_dummy_628))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0653 (g : Var) :
    (nb078_alpha_dummy_631 g) ∈
      (((Class.cv (nb078_alpha_dummy_631 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_631 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0654 :
    (nb078_alpha_dummy_629) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_628)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_629)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0655 (g : Var) :
    (nb078_alpha_dummy_632 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_631 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_632 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0656 :
    (nb078_alpha_dummy_629) ∈
      (((Class.cv (nb078_alpha_dummy_629))).fv ∪ ((Class.cv (nb078_alpha_dummy_629))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0657 (g : Var) :
    (nb078_alpha_dummy_632 g) ∈
      (((Class.cv (nb078_alpha_dummy_632 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_632 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0658 :
    (nb078_alpha_dummy_571) ∈
      (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0659 :
    (nb078_alpha_dummy_571) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_613) from (by
          unfold nb078_alpha_dummy_613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_614) from (by
            unfold nb078_alpha_dummy_614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0660 (g : Var) :
    (nb078_alpha_dummy_574 g) ∈
      (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_574 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0661 (g : Var) :
    (nb078_alpha_dummy_574 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_615 g) from (by
          unfold nb078_alpha_dummy_615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_616 g) from (by
            unfold nb078_alpha_dummy_616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0662 :
    (nb078_alpha_dummy_571) ∈
      (((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_613) from (by
          unfold nb078_alpha_dummy_613;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_614) from (by
            unfold nb078_alpha_dummy_614;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0658) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0663 (g : Var) :
    (nb078_alpha_dummy_574 g) ∈
      (((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_615 g) from (by
          unfold nb078_alpha_dummy_615;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_616 g) from (by
            unfold nb078_alpha_dummy_616;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0660 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0664 :
    (nb078_alpha_dummy_614) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0665 (g : Var) :
    (nb078_alpha_dummy_616 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0666 :
    (nb078_alpha_dummy_614) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0667 (g : Var) :
    (nb078_alpha_dummy_616 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0668 :
    (nb078_alpha_dummy_649) ∈
      (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_650))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_649)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0669 (g : Var) :
    (nb078_alpha_dummy_651 g) ∈
      (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g))
            (Class.cv (nb078_alpha_dummy_651 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0670 :
    (nb078_alpha_dummy_650) ∈
      (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_650))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_649)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0671 (g : Var) :
    (nb078_alpha_dummy_652 g) ∈
      (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g))
            (Class.cv (nb078_alpha_dummy_651 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0672 :
    (nb078_alpha_dummy_649) ∈
      (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0673 :
    (nb078_alpha_dummy_649) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_655) from (by
          unfold nb078_alpha_dummy_655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_656) from (by
            unfold nb078_alpha_dummy_656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0674 (g : Var) :
    (nb078_alpha_dummy_651 g) ∈
      (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0675 (g : Var) :
    (nb078_alpha_dummy_651 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_657 g) from (by
          unfold nb078_alpha_dummy_657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_658 g) from (by
            unfold nb078_alpha_dummy_658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0676 :
    (nb078_alpha_dummy_649) ∈
      (((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_655) from (by
          unfold nb078_alpha_dummy_655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_656) from (by
            unfold nb078_alpha_dummy_656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0672) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0677 (g : Var) :
    (nb078_alpha_dummy_651 g) ∈
      (((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_657 g) from (by
          unfold nb078_alpha_dummy_657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_658 g) from (by
            unfold nb078_alpha_dummy_658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0674 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0678 :
    (nb078_alpha_dummy_656) ∈ (((Class.cv (nb078_alpha_dummy_656))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0679 (g : Var) :
    (nb078_alpha_dummy_658 g) ∈ (((Class.cv (nb078_alpha_dummy_658 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0680 :
    (nb078_alpha_dummy_663) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_663))).fv) :=
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
    (nb078_alpha_dummy_665 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_665 g))).fv) :=
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
    (nb078_alpha_dummy_663) ∈
      (((Class.cv (nb078_alpha_dummy_663))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0683 (g : Var) :
    (nb078_alpha_dummy_665 g) ∈
      (((Class.cv (nb078_alpha_dummy_665 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0684 :
    (nb078_alpha_dummy_670) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_670))
            (Class.cv (nb078_alpha_dummy_671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0685 (g : Var) :
    (nb078_alpha_dummy_673 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0686 :
    (nb078_alpha_dummy_670) ∈
      (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0687 (g : Var) :
    (nb078_alpha_dummy_673 g) ∈
      (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0688 :
    (nb078_alpha_dummy_671) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_670))
            (Class.cv (nb078_alpha_dummy_671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0689 (g : Var) :
    (nb078_alpha_dummy_674 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g))
            (Class.cv (nb078_alpha_dummy_674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0690 :
    (nb078_alpha_dummy_671) ∈
      (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0691 (g : Var) :
    (nb078_alpha_dummy_674 g) ∈
      (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0692 :
    (nb078_alpha_dummy_670) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0693 (g : Var) :
    (nb078_alpha_dummy_673 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0694 :
    (nb078_alpha_dummy_670) ∈
      (((Class.cv (nb078_alpha_dummy_670))).fv ∪ ((Class.cv (nb078_alpha_dummy_670))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0695 (g : Var) :
    (nb078_alpha_dummy_673 g) ∈
      (((Class.cv (nb078_alpha_dummy_673 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_673 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0696 :
    (nb078_alpha_dummy_671) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_670)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_671)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0697 (g : Var) :
    (nb078_alpha_dummy_674 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0698 :
    (nb078_alpha_dummy_671) ∈
      (((Class.cv (nb078_alpha_dummy_671))).fv ∪ ((Class.cv (nb078_alpha_dummy_671))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0699 (g : Var) :
    (nb078_alpha_dummy_674 g) ∈
      (((Class.cv (nb078_alpha_dummy_674 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_674 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0700 :
    (nb078_alpha_dummy_650) ∈
      (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0701 :
    (nb078_alpha_dummy_650) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_656)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_655)
              (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_655) from (by
          unfold nb078_alpha_dummy_655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_656) from (by
            unfold nb078_alpha_dummy_656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0702 (g : Var) :
    (nb078_alpha_dummy_652 g) ∈
      (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_652 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0703 (g : Var) :
    (nb078_alpha_dummy_652 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_657 g)
              (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_657 g) from (by
          unfold nb078_alpha_dummy_657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_658 g) from (by
            unfold nb078_alpha_dummy_658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0704 :
    (nb078_alpha_dummy_650) ∈
      (((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_655) from (by
          unfold nb078_alpha_dummy_655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_656) from (by
            unfold nb078_alpha_dummy_656;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0700) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0705 (g : Var) :
    (nb078_alpha_dummy_652 g) ∈
      (((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_657 g) from (by
          unfold nb078_alpha_dummy_657;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_658 g) from (by
            unfold nb078_alpha_dummy_658;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0702 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0706 :
    (nb078_alpha_dummy_656) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0707 (g : Var) :
    (nb078_alpha_dummy_658 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0708 :
    (nb078_alpha_dummy_656) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0709 (g : Var) :
    (nb078_alpha_dummy_658 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0710 :
    (nb078_alpha_dummy_650) ∈
      (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0711 :
    (nb078_alpha_dummy_650) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_691) from (by
          unfold nb078_alpha_dummy_691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_692) from (by
            unfold nb078_alpha_dummy_692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0712 (g : Var) :
    (nb078_alpha_dummy_652 g) ∈
      (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0713 (g : Var) :
    (nb078_alpha_dummy_652 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_693 g) from (by
          unfold nb078_alpha_dummy_693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_694 g) from (by
            unfold nb078_alpha_dummy_694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0714 :
    (nb078_alpha_dummy_650) ∈
      (((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_691) from (by
          unfold nb078_alpha_dummy_691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_692) from (by
            unfold nb078_alpha_dummy_692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0715 (g : Var) :
    (nb078_alpha_dummy_652 g) ∈
      (((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_693 g) from (by
          unfold nb078_alpha_dummy_693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_694 g) from (by
            unfold nb078_alpha_dummy_694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0716 :
    (nb078_alpha_dummy_692) ∈ (((Class.cv (nb078_alpha_dummy_692))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0717 (g : Var) :
    (nb078_alpha_dummy_694 g) ∈ (((Class.cv (nb078_alpha_dummy_694 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0718 :
    (nb078_alpha_dummy_699) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_699))).fv) :=
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
    (nb078_alpha_dummy_701 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_701 g))).fv) :=
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
    (nb078_alpha_dummy_699) ∈
      (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0721 (g : Var) :
    (nb078_alpha_dummy_701 g) ∈
      (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0722 :
    (nb078_alpha_dummy_706) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_706))
            (Class.cv (nb078_alpha_dummy_707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0723 (g : Var) :
    (nb078_alpha_dummy_709 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0724 :
    (nb078_alpha_dummy_706) ∈
      (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0725 (g : Var) :
    (nb078_alpha_dummy_709 g) ∈
      (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0726 :
    (nb078_alpha_dummy_707) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_706))
            (Class.cv (nb078_alpha_dummy_707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0727 (g : Var) :
    (nb078_alpha_dummy_710 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g))
            (Class.cv (nb078_alpha_dummy_710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0728 :
    (nb078_alpha_dummy_707) ∈
      (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0729 (g : Var) :
    (nb078_alpha_dummy_710 g) ∈
      (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0730 :
    (nb078_alpha_dummy_706) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0731 (g : Var) :
    (nb078_alpha_dummy_709 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0732 :
    (nb078_alpha_dummy_706) ∈
      (((Class.cv (nb078_alpha_dummy_706))).fv ∪ ((Class.cv (nb078_alpha_dummy_706))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0733 (g : Var) :
    (nb078_alpha_dummy_709 g) ∈
      (((Class.cv (nb078_alpha_dummy_709 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_709 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0734 :
    (nb078_alpha_dummy_707) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0735 (g : Var) :
    (nb078_alpha_dummy_710 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0736 :
    (nb078_alpha_dummy_707) ∈
      (((Class.cv (nb078_alpha_dummy_707))).fv ∪ ((Class.cv (nb078_alpha_dummy_707))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0737 (g : Var) :
    (nb078_alpha_dummy_710 g) ∈
      (((Class.cv (nb078_alpha_dummy_710 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_710 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0738 :
    (nb078_alpha_dummy_649) ∈
      (((Class.cv (nb078_alpha_dummy_650))).fv ∪ ((Class.cv (nb078_alpha_dummy_649))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0739 :
    (nb078_alpha_dummy_649) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_691) from (by
          unfold nb078_alpha_dummy_691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_692) from (by
            unfold nb078_alpha_dummy_692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0740 (g : Var) :
    (nb078_alpha_dummy_651 g) ∈
      (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv) :=
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
    (nb078_alpha_dummy_651 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_693 g) from (by
          unfold nb078_alpha_dummy_693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_694 g) from (by
            unfold nb078_alpha_dummy_694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0742 :
    (nb078_alpha_dummy_649) ∈
      (((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_691) from (by
          unfold nb078_alpha_dummy_691;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_692) from (by
            unfold nb078_alpha_dummy_692;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0738) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0743 (g : Var) :
    (nb078_alpha_dummy_651 g) ∈
      (((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_693 g) from (by
          unfold nb078_alpha_dummy_693;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_694 g) from (by
            unfold nb078_alpha_dummy_694;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0740 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0744 :
    (nb078_alpha_dummy_692) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0745 (g : Var) :
    (nb078_alpha_dummy_694 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0746 :
    (nb078_alpha_dummy_692) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0747 (g : Var) :
    (nb078_alpha_dummy_694 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0748 :
    (nb078_alpha_dummy_001) ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv) :=
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
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))
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

theorem nb078_support_mem_0750 :
    (nb078_alpha_dummy_001) ∈
      (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv) :=
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
      (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪
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

theorem nb078_support_mem_0752 :
    (nb078_alpha_dummy_001) ∈
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0753 :
    (nb078_alpha_dummy_001) ∈
      (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))
                (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_570)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_571) from (by
          unfold nb078_alpha_dummy_571;
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
    g ∈ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0755 (g : Var) :
    g ∈
      (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_572 g))
                (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_573 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb078_alpha_dummy_574 g) from (by
          unfold nb078_alpha_dummy_574;
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
    (nb078_alpha_dummy_001) ∈
      (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_650))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_649)))).fv) :=
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
      (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g))
            (Class.cv (nb078_alpha_dummy_651 g)))).fv) :=
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
    (nb078_alpha_dummy_001) ∈ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0759 (g : Var) : g ∈ (((syn_ccnv (Class.cv g))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0760 :
    (nb078_alpha_dummy_571) ∈
      (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0761 :
    (nb078_alpha_dummy_571) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_727) from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_728) from (by
            unfold nb078_alpha_dummy_728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0762 (g : Var) :
    (nb078_alpha_dummy_574 g) ∈
      (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0763 (g : Var) :
    (nb078_alpha_dummy_574 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_730 g) from (by
            unfold nb078_alpha_dummy_730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0764 :
    (nb078_alpha_dummy_571) ∈
      (((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_727) from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_728) from (by
            unfold nb078_alpha_dummy_728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0765 (g : Var) :
    (nb078_alpha_dummy_574 g) ∈
      (((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_730 g) from (by
            unfold nb078_alpha_dummy_730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0766 :
    (nb078_alpha_dummy_728) ∈ (((Class.cv (nb078_alpha_dummy_728))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0767 (g : Var) :
    (nb078_alpha_dummy_730 g) ∈ (((Class.cv (nb078_alpha_dummy_730 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0768 :
    (nb078_alpha_dummy_735) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_735))).fv) :=
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
    (nb078_alpha_dummy_737 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_737 g))).fv) :=
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
    (nb078_alpha_dummy_735) ∈
      (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0771 (g : Var) :
    (nb078_alpha_dummy_737 g) ∈
      (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0772 :
    (nb078_alpha_dummy_742) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_742))
            (Class.cv (nb078_alpha_dummy_743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0773 (g : Var) :
    (nb078_alpha_dummy_745 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0774 :
    (nb078_alpha_dummy_742) ∈
      (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0775 (g : Var) :
    (nb078_alpha_dummy_745 g) ∈
      (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0776 :
    (nb078_alpha_dummy_743) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_742))
            (Class.cv (nb078_alpha_dummy_743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0777 (g : Var) :
    (nb078_alpha_dummy_746 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g))
            (Class.cv (nb078_alpha_dummy_746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0778 :
    (nb078_alpha_dummy_743) ∈
      (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0779 (g : Var) :
    (nb078_alpha_dummy_746 g) ∈
      (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0780 :
    (nb078_alpha_dummy_742) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0781 (g : Var) :
    (nb078_alpha_dummy_745 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0782 :
    (nb078_alpha_dummy_742) ∈
      (((Class.cv (nb078_alpha_dummy_742))).fv ∪ ((Class.cv (nb078_alpha_dummy_742))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0783 (g : Var) :
    (nb078_alpha_dummy_745 g) ∈
      (((Class.cv (nb078_alpha_dummy_745 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_745 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0784 :
    (nb078_alpha_dummy_743) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0785 (g : Var) :
    (nb078_alpha_dummy_746 g) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0786 :
    (nb078_alpha_dummy_743) ∈
      (((Class.cv (nb078_alpha_dummy_743))).fv ∪ ((Class.cv (nb078_alpha_dummy_743))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0787 (g : Var) :
    (nb078_alpha_dummy_746 g) ∈
      (((Class.cv (nb078_alpha_dummy_746 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_746 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0788 :
    (nb078_alpha_dummy_570) ∈
      (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0789 :
    (nb078_alpha_dummy_570) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_727) from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_728) from (by
            unfold nb078_alpha_dummy_728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0790 (g : Var) :
    (nb078_alpha_dummy_573 g) ∈
      (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0791 (g : Var) :
    (nb078_alpha_dummy_573 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_730 g) from (by
            unfold nb078_alpha_dummy_730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0792 :
    (nb078_alpha_dummy_570) ∈
      (((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_727) from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_728) from (by
            unfold nb078_alpha_dummy_728;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0788) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0793 (g : Var) :
    (nb078_alpha_dummy_573 g) ∈
      (((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_730 g) from (by
            unfold nb078_alpha_dummy_730;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0790 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0794 :
    (nb078_alpha_dummy_728) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0795 (g : Var) :
    (nb078_alpha_dummy_730 g) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0796 :
    (nb078_alpha_dummy_728) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0797 (g : Var) :
    (nb078_alpha_dummy_730 g) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0798 :
    (nb078_alpha_dummy_767) ∈
      (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769))
                (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0799 (h : Var) :
    (nb078_alpha_dummy_770 h) ∈
      (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_772 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h)
                (Class.cv (nb078_alpha_dummy_771 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0800 :
    (nb078_alpha_dummy_768) ∈
      (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769))
                (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0801 (h : Var) :
    (nb078_alpha_dummy_771 h) ∈
      (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_772 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h)
                (Class.cv (nb078_alpha_dummy_771 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0802 :
    (nb078_alpha_dummy_767) ∈
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0803 :
    (nb078_alpha_dummy_767) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_775) from (by
          unfold nb078_alpha_dummy_775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_776) from (by
            unfold nb078_alpha_dummy_776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0804 (h : Var) :
    (nb078_alpha_dummy_770 h) ∈
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0805 (h : Var) :
    (nb078_alpha_dummy_770 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_777 h) from (by
          unfold nb078_alpha_dummy_777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_778 h) from (by
            unfold nb078_alpha_dummy_778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0806 :
    (nb078_alpha_dummy_767) ∈
      (((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_775) from (by
          unfold nb078_alpha_dummy_775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_776) from (by
            unfold nb078_alpha_dummy_776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0807 (h : Var) :
    (nb078_alpha_dummy_770 h) ∈
      (((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_777 h) from (by
          unfold nb078_alpha_dummy_777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_778 h) from (by
            unfold nb078_alpha_dummy_778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0808 :
    (nb078_alpha_dummy_776) ∈ (((Class.cv (nb078_alpha_dummy_776))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0809 (h : Var) :
    (nb078_alpha_dummy_778 h) ∈ (((Class.cv (nb078_alpha_dummy_778 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0810 :
    (nb078_alpha_dummy_783) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_783))).fv) :=
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
    (nb078_alpha_dummy_785 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_785 h))).fv) :=
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
    (nb078_alpha_dummy_783) ∈
      (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0813 (h : Var) :
    (nb078_alpha_dummy_785 h) ∈
      (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0814 :
    (nb078_alpha_dummy_790) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_790))
            (Class.cv (nb078_alpha_dummy_791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0815 (h : Var) :
    (nb078_alpha_dummy_793 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0816 :
    (nb078_alpha_dummy_790) ∈
      (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0817 (h : Var) :
    (nb078_alpha_dummy_793 h) ∈
      (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0818 :
    (nb078_alpha_dummy_791) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_790))
            (Class.cv (nb078_alpha_dummy_791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0819 (h : Var) :
    (nb078_alpha_dummy_794 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h))
            (Class.cv (nb078_alpha_dummy_794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0820 :
    (nb078_alpha_dummy_791) ∈
      (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0821 (h : Var) :
    (nb078_alpha_dummy_794 h) ∈
      (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0822 :
    (nb078_alpha_dummy_790) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0823 (h : Var) :
    (nb078_alpha_dummy_793 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0824 :
    (nb078_alpha_dummy_790) ∈
      (((Class.cv (nb078_alpha_dummy_790))).fv ∪ ((Class.cv (nb078_alpha_dummy_790))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0825 (h : Var) :
    (nb078_alpha_dummy_793 h) ∈
      (((Class.cv (nb078_alpha_dummy_793 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_793 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0826 :
    (nb078_alpha_dummy_791) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0827 (h : Var) :
    (nb078_alpha_dummy_794 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0828 :
    (nb078_alpha_dummy_791) ∈
      (((Class.cv (nb078_alpha_dummy_791))).fv ∪ ((Class.cv (nb078_alpha_dummy_791))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0829 (h : Var) :
    (nb078_alpha_dummy_794 h) ∈
      (((Class.cv (nb078_alpha_dummy_794 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_794 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0830 :
    (nb078_alpha_dummy_768) ∈
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0831 :
    (nb078_alpha_dummy_768) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_775) from (by
          unfold nb078_alpha_dummy_775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_776) from (by
            unfold nb078_alpha_dummy_776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0832 (h : Var) :
    (nb078_alpha_dummy_771 h) ∈
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0833 (h : Var) :
    (nb078_alpha_dummy_771 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_777 h) from (by
          unfold nb078_alpha_dummy_777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_778 h) from (by
            unfold nb078_alpha_dummy_778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0834 :
    (nb078_alpha_dummy_768) ∈
      (((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_775) from (by
          unfold nb078_alpha_dummy_775;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_776) from (by
            unfold nb078_alpha_dummy_776;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0835 (h : Var) :
    (nb078_alpha_dummy_771 h) ∈
      (((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_777 h) from (by
          unfold nb078_alpha_dummy_777;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_778 h) from (by
            unfold nb078_alpha_dummy_778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0836 :
    (nb078_alpha_dummy_776) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0837 (h : Var) :
    (nb078_alpha_dummy_778 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0838 :
    (nb078_alpha_dummy_776) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0839 (h : Var) :
    (nb078_alpha_dummy_778 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0840 :
    (nb078_alpha_dummy_767) ∈
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0841 :
    (nb078_alpha_dummy_767) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_811) from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_812) from (by
            unfold nb078_alpha_dummy_812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0842 (h : Var) :
    (nb078_alpha_dummy_770 h) ∈
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0843 (h : Var) :
    (nb078_alpha_dummy_770 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_814 h) from (by
            unfold nb078_alpha_dummy_814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0844 :
    (nb078_alpha_dummy_767) ∈
      (((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_811) from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_812) from (by
            unfold nb078_alpha_dummy_812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0845 (h : Var) :
    (nb078_alpha_dummy_770 h) ∈
      (((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_814 h) from (by
            unfold nb078_alpha_dummy_814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0846 :
    (nb078_alpha_dummy_812) ∈ (((Class.cv (nb078_alpha_dummy_812))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0847 (h : Var) :
    (nb078_alpha_dummy_814 h) ∈ (((Class.cv (nb078_alpha_dummy_814 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0848 :
    (nb078_alpha_dummy_819) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_819))).fv) :=
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
    (nb078_alpha_dummy_821 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_821 h))).fv) :=
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
    (nb078_alpha_dummy_819) ∈
      (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0851 (h : Var) :
    (nb078_alpha_dummy_821 h) ∈
      (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0852 :
    (nb078_alpha_dummy_826) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_826))
            (Class.cv (nb078_alpha_dummy_827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0853 (h : Var) :
    (nb078_alpha_dummy_829 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0854 :
    (nb078_alpha_dummy_826) ∈
      (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0855 (h : Var) :
    (nb078_alpha_dummy_829 h) ∈
      (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0856 :
    (nb078_alpha_dummy_827) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_826))
            (Class.cv (nb078_alpha_dummy_827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0857 (h : Var) :
    (nb078_alpha_dummy_830 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h))
            (Class.cv (nb078_alpha_dummy_830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0858 :
    (nb078_alpha_dummy_827) ∈
      (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0859 (h : Var) :
    (nb078_alpha_dummy_830 h) ∈
      (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0860 :
    (nb078_alpha_dummy_826) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0861 (h : Var) :
    (nb078_alpha_dummy_829 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0862 :
    (nb078_alpha_dummy_826) ∈
      (((Class.cv (nb078_alpha_dummy_826))).fv ∪ ((Class.cv (nb078_alpha_dummy_826))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0863 (h : Var) :
    (nb078_alpha_dummy_829 h) ∈
      (((Class.cv (nb078_alpha_dummy_829 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_829 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0864 :
    (nb078_alpha_dummy_827) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0865 (h : Var) :
    (nb078_alpha_dummy_830 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0866 :
    (nb078_alpha_dummy_827) ∈
      (((Class.cv (nb078_alpha_dummy_827))).fv ∪ ((Class.cv (nb078_alpha_dummy_827))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0867 (h : Var) :
    (nb078_alpha_dummy_830 h) ∈
      (((Class.cv (nb078_alpha_dummy_830 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_830 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0868 :
    (nb078_alpha_dummy_769) ∈
      (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0869 :
    (nb078_alpha_dummy_769) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_811) from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_812) from (by
            unfold nb078_alpha_dummy_812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0870 (h : Var) :
    (nb078_alpha_dummy_772 h) ∈
      (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0871 (h : Var) :
    (nb078_alpha_dummy_772 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_814 h) from (by
            unfold nb078_alpha_dummy_814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0872 :
    (nb078_alpha_dummy_769) ∈
      (((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_811) from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_812) from (by
            unfold nb078_alpha_dummy_812;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0868) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0873 (h : Var) :
    (nb078_alpha_dummy_772 h) ∈
      (((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_814 h) from (by
            unfold nb078_alpha_dummy_814;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0870 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0874 :
    (nb078_alpha_dummy_812) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0875 (h : Var) :
    (nb078_alpha_dummy_814 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0876 :
    (nb078_alpha_dummy_812) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0877 (h : Var) :
    (nb078_alpha_dummy_814 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
