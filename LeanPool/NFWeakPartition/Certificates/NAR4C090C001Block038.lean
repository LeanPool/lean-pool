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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0084`. -/
@[expose]
noncomputable def nb090SplitAlpha0084 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy623 A), (nb090AlphaDummy624 v u h)),
        ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy623 A))
          (Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy623 A))
            (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCphi (Class.cv (nb090AlphaDummy618 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy624 v u h))
          (Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy624 v u h))
            (Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
                (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy618 A) from (by
                      unfold nb090AlphaDummy618;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
                  (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy620 v u h) from (by
                      unfold nb090AlphaDummy620;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy617 A) from (by
                        unfold nb090AlphaDummy617;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
                    (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy619 v u h) from (by
                        unfold nb090AlphaDummy619;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy623 A) from (by
                          unfold nb090AlphaDummy623;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0648 A) 0))))
                      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy624 v u h) from
                        (by
                          unfold nb090AlphaDummy624;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0649 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy621 A) from (by
                            unfold nb090AlphaDummy621;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0645 A) 0)))) (show
                          (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy622 v u h) from (by
                            unfold nb090AlphaDummy622;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0647 v u h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCfv (synC1st)
                                        (Class.cv (nb090AlphaDummy001 A)))).fv ∪
                                  ((synCfv (synC1st)
                                      (Class.cv (nb090AlphaDummy002 A)))).fv ∪
                                ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
                              ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
                                  ((synCfv (synC1st) (Class.cv v))).fv ∪
                                ((synCfv (synC2nd) (Class.cv u))).fv ∪
                              ((synCfv (synC2nd) (Class.cv v))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy041 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy042 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
                      ((Class.cv (nb090AlphaDummy044 v u h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy625 A) from (by
                              unfold nb090AlphaDummy625;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0650 A) 0)))) (show
                            (nb090AlphaDummy620 v u h) ≠ (nb090AlphaDummy627 v u h) from
                            (by
                              unfold nb090AlphaDummy627;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0651 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy626 A) from (by
                                unfold nb090AlphaDummy626;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0650 A) 1)))) (show
                              (nb090AlphaDummy620 v u h) ≠ (nb090AlphaDummy628 v u h) from
                              (by
                                unfold nb090AlphaDummy628;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0651 v u h)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy618 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb090AlphaDummy620 v u h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy632 A) from (by
          unfold nb090AlphaDummy632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A) 1)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy635 v u h) from (by
          unfold nb090AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy631 A) from (by
          unfold nb090AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A) 0)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy634 v u h) from (by
          unfold nb090AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A)
                  0)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy630 v u h) from
        (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A),
        (nb090AlphaDummy634 v u h)), ((nb090AlphaDummy629 A),
        (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy623 A),
        (nb090AlphaDummy624 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A),
        (nb090AlphaDummy634 v u h)), ((nb090AlphaDummy629 A),
        (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy623 A),
        (nb090AlphaDummy624 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy632
        A) ≠ (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A) from
                                      (by
                                        unfold nb090AlphaDummy629;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0652 A)
                                                0)))) (show (nb090AlphaDummy627 v u h) ≠
                                        (nb090AlphaDummy630 v u h) from (by
                                        unfold nb090AlphaDummy630;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0653 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
                                    ((nb090AlphaDummy625 A), (nb090AlphaDummy627 v u h)),
                                    ((nb090AlphaDummy626 A), (nb090AlphaDummy628 v u h)),
                                    ((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)),
                                    ((nb090AlphaDummy617 A), (nb090AlphaDummy619 v u h)),
                                    ((nb090AlphaDummy623 A), (nb090AlphaDummy624 v u h)),
                                    ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A) from
                                    (by
                                      unfold nb090AlphaDummy629;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0652 A)
                                              0)))) (show (nb090AlphaDummy627 v u h) ≠
                                      (nb090AlphaDummy630 v u h) from (by
                                      unfold nb090AlphaDummy630;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0653 v u h) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A) from
                                      (by
                                        unfold nb090AlphaDummy629;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0652 A)
                                                0)))) (show (nb090AlphaDummy627 v u h) ≠
                                        (nb090AlphaDummy630 v u h) from (by
                                        unfold nb090AlphaDummy630;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0653 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
                                    ((nb090AlphaDummy625 A), (nb090AlphaDummy627 v u h)),
                                    ((nb090AlphaDummy626 A), (nb090AlphaDummy628 v u h)),
                                    ((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)),
                                    ((nb090AlphaDummy617 A), (nb090AlphaDummy619 v u h)),
                                    ((nb090AlphaDummy623 A), (nb090AlphaDummy624 v u h)),
                                    ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy618 A) from (by
                        unfold nb090AlphaDummy618;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
                    (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy620 v u h) from (by
                        unfold nb090AlphaDummy620;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy617 A) from (by
                          unfold nb090AlphaDummy617;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
                      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy619 v u h) from
                        (by
                          unfold nb090AlphaDummy619;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy623 A) from (by
                            unfold nb090AlphaDummy623;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0648 A) 0)))) (show
                          (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy624 v u h) from (by
                            unfold nb090AlphaDummy624;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0649 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy621 A) from (by
                              unfold nb090AlphaDummy621;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0645 A) 0)))) (show
                            (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy622 v u h) from
                            (by
                              unfold nb090AlphaDummy622;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0647 v u h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCfv (synC1st)
        (Class.cv (nb090AlphaDummy001 A)))).fv ∪ ((synCfv (synC1st)
                                        (Class.cv (nb090AlphaDummy002 A)))).fv ∪
                                  ((synCfv (synC2nd)
                                      (Class.cv (nb090AlphaDummy001 A)))).fv ∪
                                ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv)
                              (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
                                      ((synCfv (synC1st) (Class.cv u))).fv ∪
                                    ((synCfv (synC1st) (Class.cv v))).fv ∪
                                  ((synCfv (synC2nd) (Class.cv u))).fv ∪
                                ((synCfv (synC2nd) (Class.cv v))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy041 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy042 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
                        ((Class.cv (nb090AlphaDummy044 v u h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy625 A) from (by
                                unfold nb090AlphaDummy625;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0650 A) 0)))) (show
                              (nb090AlphaDummy620 v u h) ≠ (nb090AlphaDummy627 v u h) from
                              (by
                                unfold nb090AlphaDummy627;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0651 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy626 A) from
                                (by
                                  unfold nb090AlphaDummy626;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0650 A) 1)))) (show
                                (nb090AlphaDummy620 v u h) ≠ (nb090AlphaDummy628 v u h)
                                from (by
                                  unfold nb090AlphaDummy628;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0651 v u h)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy618 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy620 v u h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy632 A) from (by
          unfold nb090AlphaDummy632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A) 1)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy635 v u h) from (by
          unfold nb090AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy631 A) from (by
          unfold nb090AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654 A)
                  0)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy634 v u h) from
        (by
          unfold nb090AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A)
                  0)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy630 v u h) from
        (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A),
        (nb090AlphaDummy634 v u h)), ((nb090AlphaDummy629 A),
        (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy623 A),
        (nb090AlphaDummy624 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A),
        (nb090AlphaDummy634 v u h)), ((nb090AlphaDummy629 A),
        (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy623 A),
        (nb090AlphaDummy624 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy632
        A) ≠ (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A)
                                        from (by
                                          unfold nb090AlphaDummy629;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0652 A) 0)))) (show
                                        (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
                                          unfold nb090AlphaDummy630;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0653 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
                                      ((nb090AlphaDummy625 A),
                                        (nb090AlphaDummy627 v u h)),
                                      ((nb090AlphaDummy626 A),
                                        (nb090AlphaDummy628 v u h)),
                                      ((nb090AlphaDummy618 A),
                                        (nb090AlphaDummy620 v u h)),
                                      ((nb090AlphaDummy617 A),
                                        (nb090AlphaDummy619 v u h)),
                                      ((nb090AlphaDummy623 A),
                                        (nb090AlphaDummy624 v u h)),
                                      ((nb090AlphaDummy621 A),
                                        (nb090AlphaDummy622 v u h)),
                                      ((nb090AlphaDummy042 A),
                                        (nb090AlphaDummy044 v u h)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A) from
                                      (by
                                        unfold nb090AlphaDummy629;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0652 A)
                                                0)))) (show (nb090AlphaDummy627 v u h) ≠
                                        (nb090AlphaDummy630 v u h) from (by
                                        unfold nb090AlphaDummy630;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0653 v u h) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A)
                                        from (by
                                          unfold nb090AlphaDummy629;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0652 A) 0)))) (show
                                        (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
                                          unfold nb090AlphaDummy630;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0653 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
                                      ((nb090AlphaDummy625 A),
                                        (nb090AlphaDummy627 v u h)),
                                      ((nb090AlphaDummy626 A),
                                        (nb090AlphaDummy628 v u h)),
                                      ((nb090AlphaDummy618 A),
                                        (nb090AlphaDummy620 v u h)),
                                      ((nb090AlphaDummy617 A),
                                        (nb090AlphaDummy619 v u h)),
                                      ((nb090AlphaDummy623 A),
                                        (nb090AlphaDummy624 v u h)),
                                      ((nb090AlphaDummy621 A),
                                        (nb090AlphaDummy622 v u h)),
                                      ((nb090AlphaDummy042 A),
                                        (nb090AlphaDummy044 v u h)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0085`. -/
@[expose]
noncomputable def nb090SplitAlpha0085 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)),
        ((nb090AlphaDummy617 A), (nb090AlphaDummy619 v u h)),
        ((nb090AlphaDummy647 A), (nb090AlphaDummy648 v u h)),
        ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy618 A))
          (Class.cv (nb090AlphaDummy042 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
            (synCun (synCphi (Class.cv (nb090AlphaDummy618 A))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy620 v u h))
          (Class.cv (nb090AlphaDummy044 v u h))) (Wff.neg
          (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
            (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy618 A) from (by
              unfold nb090AlphaDummy618;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))))
          (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy620 v u h) from (by
              unfold nb090AlphaDummy620;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))))
          (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy617 A) from (by
                unfold nb090AlphaDummy617;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))))
            (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy619 v u h) from (by
                unfold nb090AlphaDummy619;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))))
            (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy647 A) from
                (by
                  unfold nb090AlphaDummy647;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0676 A) 0))))
              (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy648 v u h) from (by
                  unfold nb090AlphaDummy648;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0677 v u h) 0))))
              (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy621 A) from
                  (by
                    unfold nb090AlphaDummy621;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0673 A) 0))))
                (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy622 v u h) from (by
                    unfold nb090AlphaDummy622;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb090_support_mem_0675 v u h) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy041 A))).fv ∪
                ((Class.cv (nb090AlphaDummy042 A))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
                ((Class.cv (nb090AlphaDummy044 v u h))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy625 A) from
                                      (by
                                        unfold nb090AlphaDummy625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0650 A)
                                                0)))) (show (nb090AlphaDummy620 v u h) ≠
                                        (nb090AlphaDummy627 v u h) from (by
                                        unfold nb090AlphaDummy627;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0651 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy618 A) ≠
        (nb090AlphaDummy626 A) from (by
                                          unfold nb090AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0650 A) 1)))) (show
                                        (nb090AlphaDummy620 v u h) ≠
        (nb090AlphaDummy628 v u h) from (by
                                          unfold nb090AlphaDummy628;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0651 v u h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy618 A) ≠
        (nb090AlphaDummy651 A) from (by
          unfold nb090AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0680 A) 0)))) (show (nb090AlphaDummy620 v u h) ≠
        (nb090AlphaDummy652 v u h) from (by
          unfold nb090AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0681 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy649 A) from (by
          unfold nb090AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0678 A) 0)))) (show (nb090AlphaDummy620 v u h) ≠
        (nb090AlphaDummy650 v u h) from (by
          unfold nb090AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0679 v u h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy618 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy620 v u h))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy632 A) from (by
          unfold nb090AlphaDummy632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  1)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy635 v u h) from
        (by
          unfold nb090AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy631 A) from (by
          unfold nb090AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  0)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy634 v u h) from
        (by
          unfold nb090AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold
            nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652
                    A)
                  0)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy630 v u h) from
        (by
          unfold
            nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A), (nb090AlphaDummy634 v u
        h)), ((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
        ((nb090AlphaDummy625 A), (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A), (nb090AlphaDummy652 v u
        h)), ((nb090AlphaDummy649 A), (nb090AlphaDummy650 v u h)),
        ((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A), (nb090AlphaDummy648 v u
        h)), ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
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
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A), (nb090AlphaDummy634 v u
        h)), ((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
        ((nb090AlphaDummy625 A), (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A), (nb090AlphaDummy652 v u
        h)), ((nb090AlphaDummy649 A), (nb090AlphaDummy650 v u h)),
        ((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A), (nb090AlphaDummy648 v u
        h)), ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy632
        A) ≠ (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A),
        (nb090AlphaDummy652 v u h)), ((nb090AlphaDummy649 A),
        (nb090AlphaDummy650 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A),
        (nb090AlphaDummy648 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A),
        (nb090AlphaDummy652 v u h)), ((nb090AlphaDummy649 A),
        (nb090AlphaDummy650 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A),
        (nb090AlphaDummy648 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy625 A) from
                                      (by
                                        unfold nb090AlphaDummy625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0650 A)
                                                0)))) (show (nb090AlphaDummy620 v u h) ≠
                                        (nb090AlphaDummy627 v u h) from (by
                                        unfold nb090AlphaDummy627;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0651 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy618 A) ≠
        (nb090AlphaDummy626 A) from (by
                                          unfold nb090AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0650 A) 1)))) (show
                                        (nb090AlphaDummy620 v u h) ≠
        (nb090AlphaDummy628 v u h) from (by
                                          unfold nb090AlphaDummy628;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0651 v u h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy618 A) ≠
        (nb090AlphaDummy651 A) from (by
          unfold nb090AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0680 A) 0)))) (show (nb090AlphaDummy620 v u h) ≠
        (nb090AlphaDummy652 v u h) from (by
          unfold nb090AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0681 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy618 A) ≠ (nb090AlphaDummy649 A) from (by
          unfold nb090AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0678 A) 0)))) (show (nb090AlphaDummy620 v u h) ≠
        (nb090AlphaDummy650 v u h) from (by
          unfold nb090AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0679 v u h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy618 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb090AlphaDummy620 v u h))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy632 A) from (by
          unfold nb090AlphaDummy632;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  1)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy635 v u h) from
        (by
          unfold nb090AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy631 A) from (by
          unfold nb090AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0654
                    A)
                  0)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy634 v u h) from
        (by
          unfold nb090AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0655
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold
            nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652
                    A)
                  0)))) (show (nb090AlphaDummy627 v u h) ≠ (nb090AlphaDummy630 v u h) from
        (by
          unfold
            nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A), (nb090AlphaDummy634 v u
        h)), ((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
        ((nb090AlphaDummy625 A), (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A), (nb090AlphaDummy652 v u
        h)), ((nb090AlphaDummy649 A), (nb090AlphaDummy650 v u h)),
        ((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A), (nb090AlphaDummy648 v u
        h)), ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
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
        (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0658
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0659
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0656
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0657
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy639 A) from (by
          unfold
            nb090AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0662
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy640 v u h) from
        (by
          unfold
            nb090AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0663
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy637 A) from (by
          unfold
            nb090AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0660
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy638 v u h) from
        (by
          unfold
            nb090AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0661
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy633 A), (nb090AlphaDummy636 v u h)), ((nb090AlphaDummy632 A),
        (nb090AlphaDummy635 v u h)), ((nb090AlphaDummy631 A), (nb090AlphaDummy634 v u
        h)), ((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)),
        ((nb090AlphaDummy625 A), (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A), (nb090AlphaDummy652 v u
        h)), ((nb090AlphaDummy649 A), (nb090AlphaDummy650 v u h)),
        ((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A), (nb090AlphaDummy648 v u
        h)), ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy632
        A) ≠ (nb090AlphaDummy643 A) from (by
          unfold
            nb090AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0666
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy644 v u h) from
        (by
          unfold
            nb090AlphaDummy644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0667
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy632 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0664
                    A)
                  0)))) (show (nb090AlphaDummy635 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0665
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy625
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy633
        A) ≠ (nb090AlphaDummy645 A) from (by
          unfold
            nb090AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0670
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy646 v u h) from
        (by
          unfold
            nb090AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0671
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy633 A) ≠
        (nb090AlphaDummy641 A) from (by
          unfold
            nb090AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0668
                    A)
                  0)))) (show (nb090AlphaDummy636 v u h) ≠ (nb090AlphaDummy642 v u h) from
        (by
          unfold
            nb090AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0669
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A),
        (nb090AlphaDummy652 v u h)), ((nb090AlphaDummy649 A),
        (nb090AlphaDummy650 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A),
        (nb090AlphaDummy648 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠ (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy625 A) ≠
        (nb090AlphaDummy629 A) from (by
          unfold nb090AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0652 A) 0)))) (show (nb090AlphaDummy627 v u h) ≠
        (nb090AlphaDummy630 v u h) from (by
          unfold nb090AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0653 v u h)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy629 A), (nb090AlphaDummy630 v u h)), ((nb090AlphaDummy625 A),
        (nb090AlphaDummy627 v u h)), ((nb090AlphaDummy626 A),
        (nb090AlphaDummy628 v u h)), ((nb090AlphaDummy651 A),
        (nb090AlphaDummy652 v u h)), ((nb090AlphaDummy649 A),
        (nb090AlphaDummy650 v u h)), ((nb090AlphaDummy618 A),
        (nb090AlphaDummy620 v u h)), ((nb090AlphaDummy617 A),
        (nb090AlphaDummy619 v u h)), ((nb090AlphaDummy647 A),
        (nb090AlphaDummy648 v u h)), ((nb090AlphaDummy621 A),
        (nb090AlphaDummy622 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb090AlphaDummy649 A), (nb090AlphaDummy650 v u h)),
                    ((nb090AlphaDummy618 A), (nb090AlphaDummy620 v u h)),
                    ((nb090AlphaDummy617 A), (nb090AlphaDummy619 v u h)),
                    ((nb090AlphaDummy647 A), (nb090AlphaDummy648 v u h)),
                    ((nb090AlphaDummy621 A), (nb090AlphaDummy622 v u h)),
                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                    ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                    ((nb090AlphaDummy001 A), u),
                    ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb090_compact_fv_empty_0512 (A : Class) :
    (nb090AlphaDummy653 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0513 (u : Var) :
    (nb090AlphaDummy654 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0514 (A : Class) :
    (nb090AlphaDummy655 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0515 (u : Var) :
    (nb090AlphaDummy656 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0516 (A : Class) :
    (nb090AlphaDummy658 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0517 (u : Var) :
    (nb090AlphaDummy660 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0518 (A : Class) :
    (nb090AlphaDummy657 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0519 (u : Var) :
    (nb090AlphaDummy659 u) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
