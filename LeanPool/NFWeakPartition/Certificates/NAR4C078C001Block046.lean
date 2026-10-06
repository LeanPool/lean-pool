/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block045

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part138`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0116`. -/
@[expose]
noncomputable def nb078SplitAlpha0116 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy843), (nb078AlphaDummy844 h)),
        ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
        ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
        ((nb078AlphaDummy841), (nb078AlphaDummy842 h)),
        ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy843))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy812)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy843)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy844 h))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy814 h)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy844 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.there
                                (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy845) from (by
                                    unfold nb078AlphaDummy845;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0876) 0)))) (show
                                  (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy846 h) from (by
                                    unfold nb078AlphaDummy846;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0877 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy843) from
                                    (by
                                      unfold nb078AlphaDummy843;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0874)
                                              0)))) (show
                                    (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy844 h) from
                                    (by
                                      unfold nb078AlphaDummy844;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0875 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy845), (nb078AlphaDummy846 h)), ((nb078AlphaDummy843),
        (nb078AlphaDummy844 h)), ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
        ((nb078AlphaDummy811), (nb078AlphaDummy813 h)), ((nb078AlphaDummy841),
        (nb078AlphaDummy842 h)), ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
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
        ((nb078AlphaDummy845), (nb078AlphaDummy846 h)), ((nb078AlphaDummy843),
        (nb078AlphaDummy844 h)), ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
        ((nb078AlphaDummy811), (nb078AlphaDummy813 h)), ((nb078AlphaDummy841),
        (nb078AlphaDummy842 h)), ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
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
                                      ((nb078AlphaDummy845), (nb078AlphaDummy846 h)),
                                      ((nb078AlphaDummy843), (nb078AlphaDummy844 h)),
                                      ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                      ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                      ((nb078AlphaDummy841), (nb078AlphaDummy842 h)),
                                      ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                                      ((nb078AlphaDummy845), (nb078AlphaDummy846 h)),
                                      ((nb078AlphaDummy843), (nb078AlphaDummy844 h)),
                                      ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                      ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                      ((nb078AlphaDummy841), (nb078AlphaDummy842 h)),
                                      ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.there
                                (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy845) from (by
                                    unfold nb078AlphaDummy845;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0876) 0)))) (show
                                  (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy846 h) from (by
                                    unfold nb078AlphaDummy846;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0877 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy812) ≠ (nb078AlphaDummy843) from
                                    (by
                                      unfold nb078AlphaDummy843;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0874)
                                              0)))) (show
                                    (nb078AlphaDummy814 h) ≠ (nb078AlphaDummy844 h) from
                                    (by
                                      unfold nb078AlphaDummy844;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0875 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy845), (nb078AlphaDummy846 h)), ((nb078AlphaDummy843),
        (nb078AlphaDummy844 h)), ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
        ((nb078AlphaDummy811), (nb078AlphaDummy813 h)), ((nb078AlphaDummy841),
        (nb078AlphaDummy842 h)), ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
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
        ((nb078AlphaDummy845), (nb078AlphaDummy846 h)), ((nb078AlphaDummy843),
        (nb078AlphaDummy844 h)), ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
        ((nb078AlphaDummy811), (nb078AlphaDummy813 h)), ((nb078AlphaDummy841),
        (nb078AlphaDummy842 h)), ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
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
                                      ((nb078AlphaDummy845), (nb078AlphaDummy846 h)),
                                      ((nb078AlphaDummy843), (nb078AlphaDummy844 h)),
                                      ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                      ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                      ((nb078AlphaDummy841), (nb078AlphaDummy842 h)),
                                      ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                                      ((nb078AlphaDummy845), (nb078AlphaDummy846 h)),
                                      ((nb078AlphaDummy843), (nb078AlphaDummy844 h)),
                                      ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
                                      ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
                                      ((nb078AlphaDummy841), (nb078AlphaDummy842 h)),
                                      ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy843), (nb078AlphaDummy844 h)),
            ((nb078AlphaDummy812), (nb078AlphaDummy814 h)),
            ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
            ((nb078AlphaDummy841), (nb078AlphaDummy842 h)),
            ((nb078AlphaDummy815), (nb078AlphaDummy816 h)),
            ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
            ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
            ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
            ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part139`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0117`. -/
@[expose]
noncomputable def nb078SplitAlpha0117 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy859))
          (Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy859)) (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCphi (Class.cv (nb078AlphaDummy854)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy860 h))
          (Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy860 h))
            (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCphi (Class.cv (nb078AlphaDummy856 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy854) from
                    (by
                      unfold nb078AlphaDummy854;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                  (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy856 h) from (by
                      unfold nb078AlphaDummy856;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy853) from
                      (by
                        unfold nb078AlphaDummy853;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                    (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy855 h) from (by
                        unfold nb078AlphaDummy855;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy859) from (by
                          unfold nb078AlphaDummy859;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy860 h) from (by
                          unfold nb078AlphaDummy860;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy857) from (by
                            unfold nb078AlphaDummy857;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy858 h) from (by
                            unfold nb078AlphaDummy858;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy847))).fv ∪
                      ((Class.cv (nb078AlphaDummy848))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy849 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy850 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from (by
                              unfold nb078AlphaDummy861;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                          (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                              unfold nb078AlphaDummy863;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from (by
                                unfold nb078AlphaDummy862;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                            (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from (by
                                unfold nb078AlphaDummy864;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from (by
          unfold nb078AlphaDummy868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy871 h) from (by
          unfold nb078AlphaDummy871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy867) from (by
          unfold nb078AlphaDummy867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
          unfold nb078AlphaDummy870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy863
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                        unfold nb078AlphaDummy865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy866 h) from (by
                                        unfold nb078AlphaDummy866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                    ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                    ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                    ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                    ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                    ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                    ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from
                                    (by
                                      unfold nb078AlphaDummy865;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0890)
                                              0)))) (show
                                    (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                    (by
                                      unfold nb078AlphaDummy866;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0891 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                        unfold nb078AlphaDummy865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy866 h) from (by
                                        unfold nb078AlphaDummy866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                    ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                    ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                    ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                    ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                    ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                    ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy854) from
                      (by
                        unfold nb078AlphaDummy854;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
                    (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy856 h) from (by
                        unfold nb078AlphaDummy856;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0884 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy853) from (by
                          unfold nb078AlphaDummy853;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0882) 0))))
                      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy855 h) from (by
                          unfold nb078AlphaDummy855;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy859) from (by
                            unfold nb078AlphaDummy859;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0886) 0))))
                        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy860 h) from (by
                            unfold nb078AlphaDummy860;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0887 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy857) from (by
                              unfold nb078AlphaDummy857;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0883) 0))))
                          (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy858 h) from (by
                              unfold nb078AlphaDummy858;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0885 h) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv)
                              (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy847))).fv ∪
                        ((Class.cv (nb078AlphaDummy848))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy849 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy850 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from (by
                                unfold nb078AlphaDummy861;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                            (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                                unfold nb078AlphaDummy863;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from (by
                                  unfold nb078AlphaDummy862;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                              (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from
                                (by
                                  unfold nb078AlphaDummy864;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy856 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from (by
          unfold nb078AlphaDummy868;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 1)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy871 h) from (by
          unfold nb078AlphaDummy871;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy867) from (by
          unfold nb078AlphaDummy867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
          unfold nb078AlphaDummy870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865)
        from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890)
                  0)))) (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy863
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from
                                        (by
                                          unfold nb078AlphaDummy865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
                                          unfold nb078AlphaDummy866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                      ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                      ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                      ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                      ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                      ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                      ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                        unfold nb078AlphaDummy865;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0890)
                                                0)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy866 h) from (by
                                        unfold nb078AlphaDummy866;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0891 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from
                                        (by
                                          unfold nb078AlphaDummy865;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0890)
                                                  0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
                                          unfold nb078AlphaDummy866;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0891 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                      ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                      ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                      ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                      ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                      ((nb078AlphaDummy859), (nb078AlphaDummy860 h)),
                                      ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part140`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0118`. -/
@[expose]
noncomputable def nb078SplitAlpha0118 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy887))
          (synCphi (Class.cv (nb078AlphaDummy854)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy887))
            (synCphi (Class.cv (nb078AlphaDummy854))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy888 h))
          (synCphi (Class.cv (nb078AlphaDummy856 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy888 h))
            (synCphi (Class.cv (nb078AlphaDummy856 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from
                    (by
                      unfold nb078AlphaDummy861;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                  (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                      unfold nb078AlphaDummy863;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from
                      (by
                        unfold nb078AlphaDummy862;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                    (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from (by
                        unfold nb078AlphaDummy864;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy887) from (by
                          unfold nb078AlphaDummy887;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                      (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy888 h) from (by
                          unfold nb078AlphaDummy888;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy885) from (by
                            unfold nb078AlphaDummy885;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                        (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy886 h) from (by
                            unfold nb078AlphaDummy886;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from (by
                                        unfold nb078AlphaDummy868;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0892)
                                                1)))) (show (nb078AlphaDummy863 h) ≠
                                        (nb078AlphaDummy871 h) from (by
                                        unfold nb078AlphaDummy871;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0893 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy867) from
                                        (by
                                          unfold nb078AlphaDummy867;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
                                          unfold nb078AlphaDummy870;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy861) ≠
        (nb078AlphaDummy865) from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy869),
        (nb078AlphaDummy872 h)), ((nb078AlphaDummy868), (nb078AlphaDummy871 h)),
                                        ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
                                        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                                        ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                                        ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                                        ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                                        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                                        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                                        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                                        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                                        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                                        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                        ((nb078AlphaDummy002), h),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)),
        ((nb078AlphaDummy868), (nb078AlphaDummy871 h)), ((nb078AlphaDummy867),
        (nb078AlphaDummy870 h)), ((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
        ((nb078AlphaDummy861), (nb078AlphaDummy863 h)), ((nb078AlphaDummy862),
        (nb078AlphaDummy864 h)), ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
        ((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                            ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                            ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                            ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                            ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                            ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                            ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                            ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                            ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                            ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                            ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                            ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                            ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                              unfold nb078AlphaDummy865;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                          (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                              unfold nb078AlphaDummy866;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                            ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                            ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                            ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                            ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                            ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                            ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                            ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                            ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                            ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                            ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                            ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                            ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy861) from (by
                        unfold nb078AlphaDummy861;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0))))
                    (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy863 h) from (by
                        unfold nb078AlphaDummy863;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0889 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy862) from (by
                          unfold nb078AlphaDummy862;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0888) 1))))
                      (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy864 h) from (by
                          unfold nb078AlphaDummy864;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0889 h) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy887) from (by
                            unfold nb078AlphaDummy887;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0918) 0))))
                        (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy888 h) from (by
                            unfold nb078AlphaDummy888;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0919 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy854) ≠ (nb078AlphaDummy885) from (by
                              unfold nb078AlphaDummy885;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0916) 0))))
                          (show (nb078AlphaDummy856 h) ≠ (nb078AlphaDummy886 h) from (by
                              unfold nb078AlphaDummy886;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0917 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy854))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy856 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy861) ≠ (nb078AlphaDummy868) from
                                        (by
                                          unfold nb078AlphaDummy868;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0892)
                                                  1)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy871 h) from (by
                                          unfold nb078AlphaDummy871;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0893 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy861) ≠
        (nb078AlphaDummy867) from (by
          unfold nb078AlphaDummy867;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0892) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy870 h) from (by
          unfold nb078AlphaDummy870;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0893 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
          unfold nb078AlphaDummy865;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0890) 0)))) (show (nb078AlphaDummy863 h) ≠
        (nb078AlphaDummy866 h) from (by
          unfold nb078AlphaDummy866;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0891 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy869),
        (nb078AlphaDummy872 h)), ((nb078AlphaDummy868), (nb078AlphaDummy871 h)),
        ((nb078AlphaDummy867), (nb078AlphaDummy870 h)), ((nb078AlphaDummy865),
        (nb078AlphaDummy866 h)), ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
        ((nb078AlphaDummy862), (nb078AlphaDummy864 h)), ((nb078AlphaDummy887),
        (nb078AlphaDummy888 h)), ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
        ((nb078AlphaDummy854), (nb078AlphaDummy856 h)), ((nb078AlphaDummy853),
        (nb078AlphaDummy855 h)), ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
        ((nb078AlphaDummy857), (nb078AlphaDummy858 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy875) from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0896)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0897
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0894)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0895
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy875)
        from (by
          unfold
            nb078AlphaDummy875;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0900)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy876 h) from (by
          unfold
            nb078AlphaDummy876;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0901
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy873)
        from (by
          unfold
            nb078AlphaDummy873;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0898)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy874 h) from (by
          unfold
            nb078AlphaDummy874;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0899
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy869), (nb078AlphaDummy872 h)), ((nb078AlphaDummy868),
        (nb078AlphaDummy871 h)), ((nb078AlphaDummy867), (nb078AlphaDummy870 h)),
        ((nb078AlphaDummy865), (nb078AlphaDummy866 h)), ((nb078AlphaDummy861),
        (nb078AlphaDummy863 h)), ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
        ((nb078AlphaDummy887), (nb078AlphaDummy888 h)), ((nb078AlphaDummy885),
        (nb078AlphaDummy886 h)), ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
        ((nb078AlphaDummy853), (nb078AlphaDummy855 h)), ((nb078AlphaDummy883),
        (nb078AlphaDummy884 h)), ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy861))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠
        (nb078AlphaDummy879) from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy879)
        from (by
          unfold
            nb078AlphaDummy879;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0904)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy880 h) from (by
          unfold
            nb078AlphaDummy880;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0905
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy868) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0902)
                  0)))) (show (nb078AlphaDummy871 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0903
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy869) ≠
        (nb078AlphaDummy881) from (by
          unfold
            nb078AlphaDummy881;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0908)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy882 h) from (by
          unfold
            nb078AlphaDummy882;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0909
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy869) ≠ (nb078AlphaDummy877)
        from (by
          unfold
            nb078AlphaDummy877;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0906)
                  0)))) (show (nb078AlphaDummy872 h) ≠ (nb078AlphaDummy878 h) from (by
          unfold
            nb078AlphaDummy878;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0907
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                  unfold nb078AlphaDummy865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                (by
                                  unfold nb078AlphaDummy866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                              ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                              ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                              ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                              ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                              ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                              ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                              ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                              ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                              ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                              ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                              ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                unfold nb078AlphaDummy865;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                            (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from (by
                                unfold nb078AlphaDummy866;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy861) ≠ (nb078AlphaDummy865) from (by
                                  unfold nb078AlphaDummy865;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0890) 0))))
                              (show (nb078AlphaDummy863 h) ≠ (nb078AlphaDummy866 h) from
                                (by
                                  unfold nb078AlphaDummy866;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0891 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy865), (nb078AlphaDummy866 h)),
                              ((nb078AlphaDummy861), (nb078AlphaDummy863 h)),
                              ((nb078AlphaDummy862), (nb078AlphaDummy864 h)),
                              ((nb078AlphaDummy887), (nb078AlphaDummy888 h)),
                              ((nb078AlphaDummy885), (nb078AlphaDummy886 h)),
                              ((nb078AlphaDummy854), (nb078AlphaDummy856 h)),
                              ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
                              ((nb078AlphaDummy883), (nb078AlphaDummy884 h)),
                              ((nb078AlphaDummy857), (nb078AlphaDummy858 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                              ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                              ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                              ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
