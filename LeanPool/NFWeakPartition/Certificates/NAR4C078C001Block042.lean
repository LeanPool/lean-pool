/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C078C001Part125Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part125`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0102`. -/
@[expose]
noncomputable def nb078SplitAlpha0102 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
        ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy781))
          (Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy781)) (Class.cab (nb078AlphaDummy775)
              (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy775))
                  (synCphi (Class.cv (nb078AlphaDummy776)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy782 h))
          (Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy782 h))
            (Class.cab (nb078AlphaDummy777 h)
              (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                  (synCphi (Class.cv (nb078AlphaDummy778 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy776) from
                    (by
                      unfold nb078AlphaDummy776;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
                  (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy778 h) from (by
                      unfold nb078AlphaDummy778;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy775) from
                      (by
                        unfold nb078AlphaDummy775;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))))
                    (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy777 h) from (by
                        unfold nb078AlphaDummy777;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0804 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy781) from (by
                          unfold nb078AlphaDummy781;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0806) 0))))
                      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy782 h) from (by
                          unfold nb078AlphaDummy782;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0807 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy779) from (by
                            unfold nb078AlphaDummy779;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0803) 0))))
                        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy780 h) from (by
                            unfold nb078AlphaDummy780;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0805 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy002))).fv ∪
                              ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078AlphaDummy767))).fv ∪
                      ((Class.cv (nb078AlphaDummy768))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy770 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy783) from (by
                              unfold nb078AlphaDummy783;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0808) 0))))
                          (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy785 h) from (by
                              unfold nb078AlphaDummy785;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0809 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy784) from (by
                                unfold nb078AlphaDummy784;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0808) 1))))
                            (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy786 h) from (by
                                unfold nb078AlphaDummy786;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0809 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy776))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy778 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy783) ≠ (nb078AlphaDummy790) from (by
          unfold nb078AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 1)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy793 h) from (by
          unfold nb078AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy789) from (by
          unfold nb078AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy792 h) from (by
          unfold nb078AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
          unfold nb078AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy788 h) from (by
          unfold nb078AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy776), (nb078AlphaDummy778 h)), ((nb078AlphaDummy775),
        (nb078AlphaDummy777 h)), ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
        ((nb078AlphaDummy779), (nb078AlphaDummy780 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy776), (nb078AlphaDummy778 h)), ((nb078AlphaDummy775),
        (nb078AlphaDummy777 h)), ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
        ((nb078AlphaDummy779), (nb078AlphaDummy780 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy783))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy785
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801) from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801)
        from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠
        (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
                                        unfold nb078AlphaDummy787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078AlphaDummy785 h) ≠
                                        (nb078AlphaDummy788 h) from (by
                                        unfold nb078AlphaDummy788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                    ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                    ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                    ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                    ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                    ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
                                    ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from
                                    (by
                                      unfold nb078AlphaDummy787;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0810)
                                              0)))) (show
                                    (nb078AlphaDummy785 h) ≠ (nb078AlphaDummy788 h) from
                                    (by
                                      unfold nb078AlphaDummy788;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0811 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
                                        unfold nb078AlphaDummy787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078AlphaDummy785 h) ≠
                                        (nb078AlphaDummy788 h) from (by
                                        unfold nb078AlphaDummy788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                    ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                    ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                    ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                    ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                    ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
                                    ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy776) from
                      (by
                        unfold nb078AlphaDummy776;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
                    (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy778 h) from (by
                        unfold nb078AlphaDummy778;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0804 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy775) from (by
                          unfold nb078AlphaDummy775;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0802) 0))))
                      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy777 h) from (by
                          unfold nb078AlphaDummy777;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0804 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy781) from (by
                            unfold nb078AlphaDummy781;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0806) 0))))
                        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy782 h) from (by
                            unfold nb078AlphaDummy782;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0807 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy779) from (by
                              unfold nb078AlphaDummy779;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0803) 0))))
                          (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy780 h) from (by
                              unfold nb078AlphaDummy780;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0805 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy002))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy767))).fv ∪
                        ((Class.cv (nb078AlphaDummy768))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy770 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy783) from (by
                                unfold nb078AlphaDummy783;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0808) 0))))
                            (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy785 h) from (by
                                unfold nb078AlphaDummy785;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0809 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy784) from (by
                                  unfold nb078AlphaDummy784;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0808) 1))))
                              (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy786 h) from
                                (by
                                  unfold nb078AlphaDummy786;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0809 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy776))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy778 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy790) from (by
          unfold nb078AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 1)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy793 h) from (by
          unfold nb078AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy789) from (by
          unfold nb078AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy792 h) from (by
          unfold nb078AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy783) ≠ (nb078AlphaDummy787)
        from (by
          unfold nb078AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810)
                  0)))) (show (nb078AlphaDummy785 h) ≠ (nb078AlphaDummy788 h) from (by
          unfold nb078AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy776), (nb078AlphaDummy778 h)), ((nb078AlphaDummy775),
        (nb078AlphaDummy777 h)), ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
        ((nb078AlphaDummy779), (nb078AlphaDummy780 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy776), (nb078AlphaDummy778 h)), ((nb078AlphaDummy775),
        (nb078AlphaDummy777 h)), ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
        ((nb078AlphaDummy779), (nb078AlphaDummy780 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy783))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy785
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801) from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801)
        from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠
        (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from
                                        (by
                                          unfold nb078AlphaDummy787;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0810)
                                                  0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy788 h) from (by
                                          unfold nb078AlphaDummy788;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0811 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                      ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                      ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                      ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                      ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                      ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
                                      ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                      ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
                                        unfold nb078AlphaDummy787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078AlphaDummy785 h) ≠
                                        (nb078AlphaDummy788 h) from (by
                                        unfold nb078AlphaDummy788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from
                                        (by
                                          unfold nb078AlphaDummy787;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0810)
                                                  0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy788 h) from (by
                                          unfold nb078AlphaDummy788;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0811 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                      ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                      ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                      ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                      ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                      ((nb078AlphaDummy781), (nb078AlphaDummy782 h)),
                                      ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                      ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part126`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0103`. -/
@[expose]
noncomputable def nb078SplitAlpha0103 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy807), (nb078AlphaDummy808 h)),
        ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
        ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
        ((nb078AlphaDummy805), (nb078AlphaDummy806 h)),
        ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy807))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy776))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy807)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy808 h))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy778 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy808 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy783) from (by
                              unfold nb078AlphaDummy783;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0808) 0))))
                          (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy785 h) from (by
                              unfold nb078AlphaDummy785;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0809 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy784) from (by
                                unfold nb078AlphaDummy784;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0808) 1))))
                            (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy786 h) from (by
                                unfold nb078AlphaDummy786;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0809 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy809) from (by
                                  unfold nb078AlphaDummy809;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0838) 0))))
                              (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy810 h) from
                                (by
                                  unfold nb078AlphaDummy810;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0839 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy807) from (by
                                    unfold nb078AlphaDummy807;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0836) 0)))) (show
                                  (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy808 h) from (by
                                    unfold nb078AlphaDummy808;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0837 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy776))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy778 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy783) ≠ (nb078AlphaDummy790) from (by
          unfold nb078AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 1)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy793 h) from (by
          unfold nb078AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy789) from (by
          unfold nb078AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy792 h) from (by
          unfold nb078AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
          unfold nb078AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy788 h) from (by
          unfold nb078AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy809), (nb078AlphaDummy810 h)), ((nb078AlphaDummy807),
        (nb078AlphaDummy808 h)), ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
        ((nb078AlphaDummy775), (nb078AlphaDummy777 h)), ((nb078AlphaDummy805),
        (nb078AlphaDummy806 h)), ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy809), (nb078AlphaDummy810 h)), ((nb078AlphaDummy807),
        (nb078AlphaDummy808 h)), ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
        ((nb078AlphaDummy775), (nb078AlphaDummy777 h)), ((nb078AlphaDummy805),
        (nb078AlphaDummy806 h)), ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy783))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy785
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801) from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801)
        from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠
        (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
                                        unfold nb078AlphaDummy787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078AlphaDummy785 h) ≠
                                        (nb078AlphaDummy788 h) from (by
                                        unfold nb078AlphaDummy788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                    ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                    ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                    ((nb078AlphaDummy809), (nb078AlphaDummy810 h)),
                                    ((nb078AlphaDummy807), (nb078AlphaDummy808 h)),
                                    ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                    ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                    ((nb078AlphaDummy805), (nb078AlphaDummy806 h)),
                                    ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from
                                    (by
                                      unfold nb078AlphaDummy787;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0810)
                                              0)))) (show
                                    (nb078AlphaDummy785 h) ≠ (nb078AlphaDummy788 h) from
                                    (by
                                      unfold nb078AlphaDummy788;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0811 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
                                        unfold nb078AlphaDummy787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078AlphaDummy785 h) ≠
                                        (nb078AlphaDummy788 h) from (by
                                        unfold nb078AlphaDummy788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                    ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                    ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                    ((nb078AlphaDummy809), (nb078AlphaDummy810 h)),
                                    ((nb078AlphaDummy807), (nb078AlphaDummy808 h)),
                                    ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                    ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                    ((nb078AlphaDummy805), (nb078AlphaDummy806 h)),
                                    ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy783) from (by
                              unfold nb078AlphaDummy783;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0808) 0))))
                          (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy785 h) from (by
                              unfold nb078AlphaDummy785;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0809 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy784) from (by
                                unfold nb078AlphaDummy784;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0808) 1))))
                            (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy786 h) from (by
                                unfold nb078AlphaDummy786;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0809 h) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy809) from (by
                                  unfold nb078AlphaDummy809;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0838) 0))))
                              (show (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy810 h) from
                                (by
                                  unfold nb078AlphaDummy810;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0839 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy776) ≠ (nb078AlphaDummy807) from (by
                                    unfold nb078AlphaDummy807;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0836) 0)))) (show
                                  (nb078AlphaDummy778 h) ≠ (nb078AlphaDummy808 h) from (by
                                    unfold nb078AlphaDummy808;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0837 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy776))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy778 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy783) ≠ (nb078AlphaDummy790) from (by
          unfold nb078AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 1)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy793 h) from (by
          unfold nb078AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy789) from (by
          unfold nb078AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy792 h) from (by
          unfold nb078AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
          unfold nb078AlphaDummy787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078AlphaDummy785 h) ≠
        (nb078AlphaDummy788 h) from (by
          unfold nb078AlphaDummy788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy809), (nb078AlphaDummy810 h)), ((nb078AlphaDummy807),
        (nb078AlphaDummy808 h)), ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
        ((nb078AlphaDummy775), (nb078AlphaDummy777 h)), ((nb078AlphaDummy805),
        (nb078AlphaDummy806 h)), ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy797) from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy797)
        from (by
          unfold
            nb078AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy798 h) from (by
          unfold
            nb078AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy795)
        from (by
          unfold
            nb078AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy796 h) from (by
          unfold
            nb078AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy791), (nb078AlphaDummy794 h)), ((nb078AlphaDummy790),
        (nb078AlphaDummy793 h)), ((nb078AlphaDummy789), (nb078AlphaDummy792 h)),
        ((nb078AlphaDummy787), (nb078AlphaDummy788 h)), ((nb078AlphaDummy783),
        (nb078AlphaDummy785 h)), ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
        ((nb078AlphaDummy809), (nb078AlphaDummy810 h)), ((nb078AlphaDummy807),
        (nb078AlphaDummy808 h)), ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
        ((nb078AlphaDummy775), (nb078AlphaDummy777 h)), ((nb078AlphaDummy805),
        (nb078AlphaDummy806 h)), ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy783))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy785
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801) from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy801)
        from (by
          unfold
            nb078AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy802 h) from (by
          unfold
            nb078AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy790) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078AlphaDummy793 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy783))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy785 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy791) ≠
        (nb078AlphaDummy803) from (by
          unfold
            nb078AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy804 h) from (by
          unfold
            nb078AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy791) ≠ (nb078AlphaDummy799)
        from (by
          unfold
            nb078AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078AlphaDummy794 h) ≠ (nb078AlphaDummy800 h) from (by
          unfold
            nb078AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
                                        unfold nb078AlphaDummy787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078AlphaDummy785 h) ≠
                                        (nb078AlphaDummy788 h) from (by
                                        unfold nb078AlphaDummy788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                    ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                    ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                    ((nb078AlphaDummy809), (nb078AlphaDummy810 h)),
                                    ((nb078AlphaDummy807), (nb078AlphaDummy808 h)),
                                    ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                    ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                    ((nb078AlphaDummy805), (nb078AlphaDummy806 h)),
                                    ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from
                                    (by
                                      unfold nb078AlphaDummy787;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0810)
                                              0)))) (show
                                    (nb078AlphaDummy785 h) ≠ (nb078AlphaDummy788 h) from
                                    (by
                                      unfold nb078AlphaDummy788;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0811 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy783) ≠ (nb078AlphaDummy787) from (by
                                        unfold nb078AlphaDummy787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078AlphaDummy785 h) ≠
                                        (nb078AlphaDummy788 h) from (by
                                        unfold nb078AlphaDummy788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy787), (nb078AlphaDummy788 h)),
                                    ((nb078AlphaDummy783), (nb078AlphaDummy785 h)),
                                    ((nb078AlphaDummy784), (nb078AlphaDummy786 h)),
                                    ((nb078AlphaDummy809), (nb078AlphaDummy810 h)),
                                    ((nb078AlphaDummy807), (nb078AlphaDummy808 h)),
                                    ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
                                    ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
                                    ((nb078AlphaDummy805), (nb078AlphaDummy806 h)),
                                    ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy807), (nb078AlphaDummy808 h)),
            ((nb078AlphaDummy776), (nb078AlphaDummy778 h)),
            ((nb078AlphaDummy775), (nb078AlphaDummy777 h)),
            ((nb078AlphaDummy805), (nb078AlphaDummy806 h)),
            ((nb078AlphaDummy779), (nb078AlphaDummy780 h)),
            ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
            ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
            ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
            ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
            ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part127`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0104`. -/
@[expose]
noncomputable def nb078SplitAlpha0104 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
        ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy817))
          (Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy817)) (Class.cab (nb078AlphaDummy811)
              (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
                (Wff.classEq (Class.cv (nb078AlphaDummy811))
                  (synCphi (Class.cv (nb078AlphaDummy812)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy818 h))
          (Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy818 h))
            (Class.cab (nb078AlphaDummy813 h)
              (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                  (synCphi (Class.cv (nb078AlphaDummy814 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy812) from
                    (by
                      unfold nb078AlphaDummy812;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
                  (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy814 h) from (by
                      unfold nb078AlphaDummy814;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy811) from
                      (by
                        unfold nb078AlphaDummy811;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))))
                    (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy813 h) from (by
                        unfold nb078AlphaDummy813;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0842 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy817) from (by
                          unfold nb078AlphaDummy817;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0844) 0))))
                      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy818 h) from (by
                          unfold nb078AlphaDummy818;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0845 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy815) from (by
                            unfold nb078AlphaDummy815;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0841) 0))))
                        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy816 h) from (by
                            unfold nb078AlphaDummy816;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0843 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy002))).fv ∪
                              ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy002))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy767))).fv ∪
                      ((Class.cv (nb078AlphaDummy769))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy770 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy772 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy819) from (by
                              unfold nb078AlphaDummy819;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0846) 0))))
                          (show (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy821 h) from (by
                              unfold nb078AlphaDummy821;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0847 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy820) from (by
                                unfold nb078AlphaDummy820;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0846) 1))))
                            (show (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy822 h) from (by
                                unfold nb078AlphaDummy822;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0847 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy812))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy814 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy819) ≠ (nb078AlphaDummy826) from (by
          unfold nb078AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 1)))) (show (nb078AlphaDummy821 h) ≠
        (nb078AlphaDummy829 h) from (by
          unfold nb078AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy819) ≠ (nb078AlphaDummy825) from (by
          unfold nb078AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 0)))) (show (nb078AlphaDummy821 h) ≠
        (nb078AlphaDummy828 h) from (by
          unfold nb078AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy819) ≠ (nb078AlphaDummy823) from (by
          unfold nb078AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0848) 0)))) (show (nb078AlphaDummy821 h) ≠
        (nb078AlphaDummy824 h) from (by
          unfold nb078AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0849 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy827), (nb078AlphaDummy830 h)), ((nb078AlphaDummy826),
        (nb078AlphaDummy829 h)), ((nb078AlphaDummy825), (nb078AlphaDummy828 h)),
        ((nb078AlphaDummy823), (nb078AlphaDummy824 h)), ((nb078AlphaDummy819),
        (nb078AlphaDummy821 h)), ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
        ((nb078AlphaDummy812), (nb078AlphaDummy814 h)), ((nb078AlphaDummy811),
        (nb078AlphaDummy813 h)), ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
        ((nb078AlphaDummy815), (nb078AlphaDummy816 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy833) from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy833)
        from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy833) from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy833)
        from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy827), (nb078AlphaDummy830 h)), ((nb078AlphaDummy826),
        (nb078AlphaDummy829 h)), ((nb078AlphaDummy825), (nb078AlphaDummy828 h)),
        ((nb078AlphaDummy823), (nb078AlphaDummy824 h)), ((nb078AlphaDummy819),
        (nb078AlphaDummy821 h)), ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
        ((nb078AlphaDummy812), (nb078AlphaDummy814 h)), ((nb078AlphaDummy811),
        (nb078AlphaDummy813 h)), ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
        ((nb078AlphaDummy815), (nb078AlphaDummy816 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy819))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy821 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy826) ≠
        (nb078AlphaDummy837) from (by
          unfold
            nb078AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy838 h) from (by
          unfold
            nb078AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy837)
        from (by
          unfold
            nb078AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy838 h) from (by
          unfold
            nb078AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy839) from (by
          unfold
            nb078AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy840 h) from (by
          unfold
            nb078AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy827) ≠
        (nb078AlphaDummy839) from (by
          unfold
            nb078AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy840 h) from (by
          unfold
            nb078AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy819) ≠ (nb078AlphaDummy823) from (by
                                        unfold nb078AlphaDummy823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078AlphaDummy821 h) ≠
                                        (nb078AlphaDummy824 h) from (by
                                        unfold nb078AlphaDummy824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy823), (nb078AlphaDummy824 h)),
                                    ((nb078AlphaDummy819), (nb078AlphaDummy821 h)),
                                    ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
                                    ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                    ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                    ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
                                    ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy819) ≠ (nb078AlphaDummy823) from
                                    (by
                                      unfold nb078AlphaDummy823;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0848)
                                              0)))) (show
                                    (nb078AlphaDummy821 h) ≠ (nb078AlphaDummy824 h) from
                                    (by
                                      unfold nb078AlphaDummy824;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0849 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy819) ≠ (nb078AlphaDummy823) from (by
                                        unfold nb078AlphaDummy823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078AlphaDummy821 h) ≠
                                        (nb078AlphaDummy824 h) from (by
                                        unfold nb078AlphaDummy824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy823), (nb078AlphaDummy824 h)),
                                    ((nb078AlphaDummy819), (nb078AlphaDummy821 h)),
                                    ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
                                    ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                    ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                    ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
                                    ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                    ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy812) from
                      (by
                        unfold nb078AlphaDummy812;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
                    (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy814 h) from (by
                        unfold nb078AlphaDummy814;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0842 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy811) from (by
                          unfold nb078AlphaDummy811;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0840) 0))))
                      (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy813 h) from (by
                          unfold nb078AlphaDummy813;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0842 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy817) from (by
                            unfold nb078AlphaDummy817;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0844) 0))))
                        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy818 h) from (by
                            unfold nb078AlphaDummy818;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0845 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy815) from (by
                              unfold nb078AlphaDummy815;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0841) 0))))
                          (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy816 h) from (by
                              unfold nb078AlphaDummy816;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0843 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078AlphaDummy002))).fv ∪
                                ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb078AlphaDummy002))).fv ∪
                                  ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy767))).fv ∪
                        ((Class.cv (nb078AlphaDummy769))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy770 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy772 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy819) from (by
                                unfold nb078AlphaDummy819;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0846) 0))))
                            (show (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy821 h) from (by
                                unfold nb078AlphaDummy821;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0847 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy820) from (by
                                  unfold nb078AlphaDummy820;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0846) 1))))
                              (show (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy822 h) from
                                (by
                                  unfold nb078AlphaDummy822;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0847 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy812))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy814 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy819) ≠ (nb078AlphaDummy826) from (by
          unfold nb078AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 1)))) (show (nb078AlphaDummy821 h) ≠
        (nb078AlphaDummy829 h) from (by
          unfold nb078AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy819) ≠ (nb078AlphaDummy825) from (by
          unfold nb078AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 0)))) (show (nb078AlphaDummy821 h) ≠
        (nb078AlphaDummy828 h) from (by
          unfold nb078AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy819) ≠ (nb078AlphaDummy823)
        from (by
          unfold nb078AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0848)
                  0)))) (show (nb078AlphaDummy821 h) ≠ (nb078AlphaDummy824 h) from (by
          unfold nb078AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0849 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy827), (nb078AlphaDummy830 h)), ((nb078AlphaDummy826),
        (nb078AlphaDummy829 h)), ((nb078AlphaDummy825), (nb078AlphaDummy828 h)),
        ((nb078AlphaDummy823), (nb078AlphaDummy824 h)), ((nb078AlphaDummy819),
        (nb078AlphaDummy821 h)), ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
        ((nb078AlphaDummy812), (nb078AlphaDummy814 h)), ((nb078AlphaDummy811),
        (nb078AlphaDummy813 h)), ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
        ((nb078AlphaDummy815), (nb078AlphaDummy816 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy833) from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy833)
        from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy833) from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy833)
        from (by
          unfold
            nb078AlphaDummy833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy834 h) from (by
          unfold
            nb078AlphaDummy834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy831)
        from (by
          unfold
            nb078AlphaDummy831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy832 h) from (by
          unfold
            nb078AlphaDummy832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy827), (nb078AlphaDummy830 h)), ((nb078AlphaDummy826),
        (nb078AlphaDummy829 h)), ((nb078AlphaDummy825), (nb078AlphaDummy828 h)),
        ((nb078AlphaDummy823), (nb078AlphaDummy824 h)), ((nb078AlphaDummy819),
        (nb078AlphaDummy821 h)), ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
        ((nb078AlphaDummy812), (nb078AlphaDummy814 h)), ((nb078AlphaDummy811),
        (nb078AlphaDummy813 h)), ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
        ((nb078AlphaDummy815), (nb078AlphaDummy816 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy819))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy821
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy826) ≠
        (nb078AlphaDummy837) from (by
          unfold
            nb078AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy838 h) from (by
          unfold
            nb078AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy837)
        from (by
          unfold
            nb078AlphaDummy837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy838 h) from (by
          unfold
            nb078AlphaDummy838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy826) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078AlphaDummy829 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy819))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy821 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy839) from (by
          unfold
            nb078AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy840 h) from (by
          unfold
            nb078AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy827) ≠
        (nb078AlphaDummy839) from (by
          unfold
            nb078AlphaDummy839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy840 h) from (by
          unfold
            nb078AlphaDummy840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy827) ≠ (nb078AlphaDummy835)
        from (by
          unfold
            nb078AlphaDummy835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078AlphaDummy830 h) ≠ (nb078AlphaDummy836 h) from (by
          unfold
            nb078AlphaDummy836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy819) ≠ (nb078AlphaDummy823) from
                                        (by
                                          unfold nb078AlphaDummy823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078AlphaDummy821 h) ≠
        (nb078AlphaDummy824 h) from (by
                                          unfold nb078AlphaDummy824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy823), (nb078AlphaDummy824 h)),
                                      ((nb078AlphaDummy819), (nb078AlphaDummy821 h)),
                                      ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
                                      ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                      ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                      ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
                                      ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                      ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy819) ≠ (nb078AlphaDummy823) from (by
                                        unfold nb078AlphaDummy823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078AlphaDummy821 h) ≠
                                        (nb078AlphaDummy824 h) from (by
                                        unfold nb078AlphaDummy824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy819) ≠ (nb078AlphaDummy823) from
                                        (by
                                          unfold nb078AlphaDummy823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078AlphaDummy821 h) ≠
        (nb078AlphaDummy824 h) from (by
                                          unfold nb078AlphaDummy824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy823), (nb078AlphaDummy824 h)),
                                      ((nb078AlphaDummy819), (nb078AlphaDummy821 h)),
                                      ((nb078AlphaDummy820), (nb078AlphaDummy822 h)),
                                      ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                      ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                      ((nb078AlphaDummy817), (nb078AlphaDummy818 h)),
                                      ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                      ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
