/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block037

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part106`. -/


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

@[expose]
noncomputable def nb090_split_alpha_0084 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)),
        ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_623 A))
          (Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_623 A))
            (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_624 v u h))
          (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_624 v u h))
            (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
                (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_618 A) from (by
                      unfold nb090_alpha_dummy_618;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
                  (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_620 v u h) from (by
                      unfold nb090_alpha_dummy_620;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_617 A) from (by
                        unfold nb090_alpha_dummy_617;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
                    (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_619 v u h) from (by
                        unfold nb090_alpha_dummy_619;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_623 A) from (by
                          unfold nb090_alpha_dummy_623;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0648 A) 0))))
                      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_624 v u h) from
                        (by
                          unfold nb090_alpha_dummy_624;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0649 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_621 A) from (by
                            unfold nb090_alpha_dummy_621;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0645 A) 0)))) (show
                          (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_622 v u h) from (by
                            unfold nb090_alpha_dummy_622;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0647 v u h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st)
                                        (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
                                  ((syn_cfv (syn_c1st)
                                      (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
                                ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
                              ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
                                  ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪
                                ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
                              ((syn_cfv (syn_c2nd) (Class.cv v))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_042 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_625 A) from (by
                              unfold nb090_alpha_dummy_625;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0650 A) 0)))) (show
                            (nb090_alpha_dummy_620 v u h) ≠ (nb090_alpha_dummy_627 v u h) from
                            (by
                              unfold nb090_alpha_dummy_627;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0651 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_626 A) from (by
                                unfold nb090_alpha_dummy_626;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0650 A) 1)))) (show
                              (nb090_alpha_dummy_620 v u h) ≠ (nb090_alpha_dummy_628 v u h) from
                              (by
                                unfold nb090_alpha_dummy_628;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0651 v u h)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_618 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_632 A) from (by
          unfold nb090_alpha_dummy_632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A) 1)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_635 v u h) from (by
          unfold nb090_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_631 A) from (by
          unfold nb090_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A) 0)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_634 v u h) from (by
          unfold nb090_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A)
                  0)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_630 v u h) from
        (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A),
        (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A),
        (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A),
        (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A),
        (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A),
        (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A),
        (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_632
        A) ≠ (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A) from
                                      (by
                                        unfold nb090_alpha_dummy_629;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0652 A)
                                                0)))) (show (nb090_alpha_dummy_627 v u h) ≠
                                        (nb090_alpha_dummy_630 v u h) from (by
                                        unfold nb090_alpha_dummy_630;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0653 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
                                    ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)),
                                    ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)),
                                    ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)),
                                    ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)),
                                    ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)),
                                    ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A) from
                                    (by
                                      unfold nb090_alpha_dummy_629;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0652 A)
                                              0)))) (show (nb090_alpha_dummy_627 v u h) ≠
                                      (nb090_alpha_dummy_630 v u h) from (by
                                      unfold nb090_alpha_dummy_630;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0653 v u h) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A) from
                                      (by
                                        unfold nb090_alpha_dummy_629;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0652 A)
                                                0)))) (show (nb090_alpha_dummy_627 v u h) ≠
                                        (nb090_alpha_dummy_630 v u h) from (by
                                        unfold nb090_alpha_dummy_630;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0653 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
                                    ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)),
                                    ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)),
                                    ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)),
                                    ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)),
                                    ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)),
                                    ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_618 A) from (by
                        unfold nb090_alpha_dummy_618;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
                    (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_620 v u h) from (by
                        unfold nb090_alpha_dummy_620;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_617 A) from (by
                          unfold nb090_alpha_dummy_617;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
                      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_619 v u h) from
                        (by
                          unfold nb090_alpha_dummy_619;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_623 A) from (by
                            unfold nb090_alpha_dummy_623;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0648 A) 0)))) (show
                          (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_624 v u h) from (by
                            unfold nb090_alpha_dummy_624;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0649 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_621 A) from (by
                              unfold nb090_alpha_dummy_621;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0645 A) 0)))) (show
                            (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_622 v u h) from
                            (by
                              unfold nb090_alpha_dummy_622;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0647 v u h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st)
        (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st)
                                        (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
                                  ((syn_cfv (syn_c2nd)
                                      (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
                                ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv)
                              (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
                                      ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
                                    ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪
                                  ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
                                ((syn_cfv (syn_c2nd) (Class.cv v))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_042 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_625 A) from (by
                                unfold nb090_alpha_dummy_625;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0650 A) 0)))) (show
                              (nb090_alpha_dummy_620 v u h) ≠ (nb090_alpha_dummy_627 v u h) from
                              (by
                                unfold nb090_alpha_dummy_627;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0651 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_626 A) from
                                (by
                                  unfold nb090_alpha_dummy_626;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0650 A) 1)))) (show
                                (nb090_alpha_dummy_620 v u h) ≠ (nb090_alpha_dummy_628 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_628;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0651 v u h)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_618 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_632 A) from (by
          unfold nb090_alpha_dummy_632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A) 1)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_635 v u h) from (by
          unfold nb090_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_631 A) from (by
          unfold nb090_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A)
                  0)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_634 v u h) from
        (by
          unfold nb090_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A)
                  0)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_630 v u h) from
        (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A),
        (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A),
        (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A),
        (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A),
        (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A),
        (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A),
        (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_632
        A) ≠ (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A)
                                        from (by
                                          unfold nb090_alpha_dummy_629;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0652 A) 0)))) (show
                                        (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
                                          unfold nb090_alpha_dummy_630;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0653 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
                                      ((nb090_alpha_dummy_625 A),
                                        (nb090_alpha_dummy_627 v u h)),
                                      ((nb090_alpha_dummy_626 A),
                                        (nb090_alpha_dummy_628 v u h)),
                                      ((nb090_alpha_dummy_618 A),
                                        (nb090_alpha_dummy_620 v u h)),
                                      ((nb090_alpha_dummy_617 A),
                                        (nb090_alpha_dummy_619 v u h)),
                                      ((nb090_alpha_dummy_623 A),
                                        (nb090_alpha_dummy_624 v u h)),
                                      ((nb090_alpha_dummy_621 A),
                                        (nb090_alpha_dummy_622 v u h)),
                                      ((nb090_alpha_dummy_042 A),
                                        (nb090_alpha_dummy_044 v u h)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A) from
                                      (by
                                        unfold nb090_alpha_dummy_629;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0652 A)
                                                0)))) (show (nb090_alpha_dummy_627 v u h) ≠
                                        (nb090_alpha_dummy_630 v u h) from (by
                                        unfold nb090_alpha_dummy_630;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0653 v u h) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A)
                                        from (by
                                          unfold nb090_alpha_dummy_629;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0652 A) 0)))) (show
                                        (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
                                          unfold nb090_alpha_dummy_630;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0653 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
                                      ((nb090_alpha_dummy_625 A),
                                        (nb090_alpha_dummy_627 v u h)),
                                      ((nb090_alpha_dummy_626 A),
                                        (nb090_alpha_dummy_628 v u h)),
                                      ((nb090_alpha_dummy_618 A),
                                        (nb090_alpha_dummy_620 v u h)),
                                      ((nb090_alpha_dummy_617 A),
                                        (nb090_alpha_dummy_619 v u h)),
                                      ((nb090_alpha_dummy_623 A),
                                        (nb090_alpha_dummy_624 v u h)),
                                      ((nb090_alpha_dummy_621 A),
                                        (nb090_alpha_dummy_622 v u h)),
                                      ((nb090_alpha_dummy_042 A),
                                        (nb090_alpha_dummy_044 v u h)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part107`. -/


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

@[expose]
noncomputable def nb090_split_alpha_0085 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)),
        ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)),
        ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)),
        ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_618 A))
          (Class.cv (nb090_alpha_dummy_042 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
            (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_620 v u h))
          (Class.cv (nb090_alpha_dummy_044 v u h))) (Wff.neg
          (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
            (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_618 A) from (by
              unfold nb090_alpha_dummy_618;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))))
          (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_620 v u h) from (by
              unfold nb090_alpha_dummy_620;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))))
          (TAlphaVar.there (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_617 A) from (by
                unfold nb090_alpha_dummy_617;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))))
            (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_619 v u h) from (by
                unfold nb090_alpha_dummy_619;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))))
            (TAlphaVar.there (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_647 A) from
                (by
                  unfold nb090_alpha_dummy_647;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0676 A) 0))))
              (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_648 v u h) from (by
                  unfold nb090_alpha_dummy_648;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0677 v u h) 0))))
              (TAlphaVar.there (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_621 A) from
                  (by
                    unfold nb090_alpha_dummy_621;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0673 A) 0))))
                (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_622 v u h) from (by
                    unfold nb090_alpha_dummy_622;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb090_support_mem_0675 v u h) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
                ((Class.cv (nb090_alpha_dummy_042 A))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
                ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_625 A) from
                                      (by
                                        unfold nb090_alpha_dummy_625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0650 A)
                                                0)))) (show (nb090_alpha_dummy_620 v u h) ≠
                                        (nb090_alpha_dummy_627 v u h) from (by
                                        unfold nb090_alpha_dummy_627;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0651 v u h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_618 A) ≠
        (nb090_alpha_dummy_626 A) from (by
                                          unfold nb090_alpha_dummy_626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0650 A) 1)))) (show
                                        (nb090_alpha_dummy_620 v u h) ≠
        (nb090_alpha_dummy_628 v u h) from (by
                                          unfold nb090_alpha_dummy_628;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0651 v u h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_618 A) ≠
        (nb090_alpha_dummy_651 A) from (by
          unfold nb090_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0680 A) 0)))) (show (nb090_alpha_dummy_620 v u h) ≠
        (nb090_alpha_dummy_652 v u h) from (by
          unfold nb090_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0681 v u h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_649 A) from (by
          unfold nb090_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0678 A) 0)))) (show (nb090_alpha_dummy_620 v u h) ≠
        (nb090_alpha_dummy_650 v u h) from (by
          unfold nb090_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0679 v u h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_618 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_620 v u h))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_632 A) from (by
          unfold nb090_alpha_dummy_632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  1)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_635 v u h) from
        (by
          unfold nb090_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_631 A) from (by
          unfold nb090_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  0)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_634 v u h) from
        (by
          unfold nb090_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold
            nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652
                    A)
                  0)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_630 v u h) from
        (by
          unfold
            nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u
        h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
        ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u
        h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)),
        ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u
        h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u
        h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
        ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u
        h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)),
        ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u
        h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_632
        A) ≠ (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A),
        (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A),
        (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A),
        (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A),
        (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A),
        (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A),
        (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_625 A) from
                                      (by
                                        unfold nb090_alpha_dummy_625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0650 A)
                                                0)))) (show (nb090_alpha_dummy_620 v u h) ≠
                                        (nb090_alpha_dummy_627 v u h) from (by
                                        unfold nb090_alpha_dummy_627;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0651 v u h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_618 A) ≠
        (nb090_alpha_dummy_626 A) from (by
                                          unfold nb090_alpha_dummy_626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0650 A) 1)))) (show
                                        (nb090_alpha_dummy_620 v u h) ≠
        (nb090_alpha_dummy_628 v u h) from (by
                                          unfold nb090_alpha_dummy_628;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0651 v u h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_618 A) ≠
        (nb090_alpha_dummy_651 A) from (by
          unfold nb090_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0680 A) 0)))) (show (nb090_alpha_dummy_620 v u h) ≠
        (nb090_alpha_dummy_652 v u h) from (by
          unfold nb090_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0681 v u h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_618 A) ≠ (nb090_alpha_dummy_649 A) from (by
          unfold nb090_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0678 A) 0)))) (show (nb090_alpha_dummy_620 v u h) ≠
        (nb090_alpha_dummy_650 v u h) from (by
          unfold nb090_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0679 v u h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_618 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090_alpha_dummy_620 v u h))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_632 A) from (by
          unfold nb090_alpha_dummy_632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  1)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_635 v u h) from
        (by
          unfold nb090_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_631 A) from (by
          unfold nb090_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  0)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_634 v u h) from
        (by
          unfold nb090_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold
            nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652
                    A)
                  0)))) (show (nb090_alpha_dummy_627 v u h) ≠ (nb090_alpha_dummy_630 v u h) from
        (by
          unfold
            nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u
        h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
        ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u
        h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)),
        ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u
        h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_639 A) from (by
          unfold
            nb090_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_640 v u h) from
        (by
          unfold
            nb090_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_637 A) from (by
          unfold
            nb090_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_638 v u h) from
        (by
          unfold
            nb090_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A),
        (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u
        h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)),
        ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A), (nb090_alpha_dummy_652 v u
        h)), ((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)),
        ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u
        h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_632
        A) ≠ (nb090_alpha_dummy_643 A) from (by
          unfold
            nb090_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_644 v u h) from
        (by
          unfold
            nb090_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_632 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090_alpha_dummy_635 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_625
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_633
        A) ≠ (nb090_alpha_dummy_645 A) from (by
          unfold
            nb090_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_646 v u h) from
        (by
          unfold
            nb090_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_633 A) ≠
        (nb090_alpha_dummy_641 A) from (by
          unfold
            nb090_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090_alpha_dummy_636 v u h) ≠ (nb090_alpha_dummy_642 v u h) from
        (by
          unfold
            nb090_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A),
        (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A),
        (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A),
        (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠ (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_625 A) ≠
        (nb090_alpha_dummy_629 A) from (by
          unfold nb090_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090_alpha_dummy_627 v u h) ≠
        (nb090_alpha_dummy_630 v u h) from (by
          unfold nb090_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A),
        (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A),
        (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_651 A),
        (nb090_alpha_dummy_652 v u h)), ((nb090_alpha_dummy_649 A),
        (nb090_alpha_dummy_650 v u h)), ((nb090_alpha_dummy_618 A),
        (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A),
        (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_647 A),
        (nb090_alpha_dummy_648 v u h)), ((nb090_alpha_dummy_621 A),
        (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb090_alpha_dummy_649 A), (nb090_alpha_dummy_650 v u h)),
                    ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)),
                    ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)),
                    ((nb090_alpha_dummy_647 A), (nb090_alpha_dummy_648 v u h)),
                    ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)),
                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                    ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                    ((nb090_alpha_dummy_001 A), u),
                    ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb090_compact_fv_empty_0512 (A : Class) :
    (nb090_alpha_dummy_653 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0513 (u : Var) :
    (nb090_alpha_dummy_654 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0514 (A : Class) :
    (nb090_alpha_dummy_655 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0515 (u : Var) :
    (nb090_alpha_dummy_656 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0516 (A : Class) :
    (nb090_alpha_dummy_658 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0517 (u : Var) :
    (nb090_alpha_dummy_660 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0518 (A : Class) :
    (nb090_alpha_dummy_657 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0519 (u : Var) :
    (nb090_alpha_dummy_659 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
