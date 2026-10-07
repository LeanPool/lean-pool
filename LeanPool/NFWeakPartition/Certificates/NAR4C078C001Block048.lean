/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block047

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part144`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0122`. -/
@[expose]
noncomputable def nb078SplitAlpha0122 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy957), (nb078AlphaDummy958 h)),
        ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
        ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
        ((nb078AlphaDummy955), (nb078AlphaDummy956 h)),
        ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy957))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy926)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy957)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy958 h))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy928 h)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy958 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy933) from (by
                                unfold nb078AlphaDummy933;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0976) 0))))
                            (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy935 h) from (by
                                unfold nb078AlphaDummy935;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0977 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy934) from (by
                                  unfold nb078AlphaDummy934;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0976) 1))))
                              (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy936 h) from
                                (by
                                  unfold nb078AlphaDummy936;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0977 h) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy959) from (by
                                    unfold nb078AlphaDummy959;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1006) 0)))) (show
                                  (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy960 h) from (by
                                    unfold nb078AlphaDummy960;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1007 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy957) from
                                    (by
                                      unfold nb078AlphaDummy957;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1004)
                                              0)))) (show
                                    (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy958 h) from
                                    (by
                                      unfold nb078AlphaDummy958;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1005 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy926))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy928 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy933) ≠ (nb078AlphaDummy940) from (by
          unfold nb078AlphaDummy940;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 1)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy943 h) from (by
          unfold nb078AlphaDummy943;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy933) ≠ (nb078AlphaDummy939) from (by
          unfold nb078AlphaDummy939;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy942 h) from (by
          unfold nb078AlphaDummy942;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937)
        from (by
          unfold nb078AlphaDummy937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978)
                  0)))) (show (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from (by
          unfold nb078AlphaDummy938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy941), (nb078AlphaDummy944 h)), ((nb078AlphaDummy940),
        (nb078AlphaDummy943 h)), ((nb078AlphaDummy939), (nb078AlphaDummy942 h)),
        ((nb078AlphaDummy937), (nb078AlphaDummy938 h)), ((nb078AlphaDummy933),
        (nb078AlphaDummy935 h)), ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
        ((nb078AlphaDummy959), (nb078AlphaDummy960 h)), ((nb078AlphaDummy957),
        (nb078AlphaDummy958 h)), ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
        ((nb078AlphaDummy925), (nb078AlphaDummy927 h)), ((nb078AlphaDummy955),
        (nb078AlphaDummy956 h)), ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy947) from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy947)
        from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy947) from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy947)
        from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy941), (nb078AlphaDummy944 h)), ((nb078AlphaDummy940),
        (nb078AlphaDummy943 h)), ((nb078AlphaDummy939), (nb078AlphaDummy942 h)),
        ((nb078AlphaDummy937), (nb078AlphaDummy938 h)), ((nb078AlphaDummy933),
        (nb078AlphaDummy935 h)), ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
        ((nb078AlphaDummy959), (nb078AlphaDummy960 h)), ((nb078AlphaDummy957),
        (nb078AlphaDummy958 h)), ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
        ((nb078AlphaDummy925), (nb078AlphaDummy927 h)), ((nb078AlphaDummy955),
        (nb078AlphaDummy956 h)), ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy935
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy940) ≠
        (nb078AlphaDummy951) from (by
          unfold
            nb078AlphaDummy951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy952 h) from (by
          unfold
            nb078AlphaDummy952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy951)
        from (by
          unfold
            nb078AlphaDummy951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy952 h) from (by
          unfold
            nb078AlphaDummy952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy953) from (by
          unfold
            nb078AlphaDummy953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy954 h) from (by
          unfold
            nb078AlphaDummy954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy941) ≠
        (nb078AlphaDummy953) from (by
          unfold
            nb078AlphaDummy953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy954 h) from (by
          unfold
            nb078AlphaDummy954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                        (by
                                          unfold nb078AlphaDummy937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
                                          unfold nb078AlphaDummy938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy937), (nb078AlphaDummy938 h)),
                                      ((nb078AlphaDummy933), (nb078AlphaDummy935 h)),
                                      ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
                                      ((nb078AlphaDummy959), (nb078AlphaDummy960 h)),
                                      ((nb078AlphaDummy957), (nb078AlphaDummy958 h)),
                                      ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                      ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                      ((nb078AlphaDummy955), (nb078AlphaDummy956 h)),
                                      ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
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
                                      (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
                                        unfold nb078AlphaDummy937;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0978)
                                                0)))) (show (nb078AlphaDummy935 h) ≠
                                        (nb078AlphaDummy938 h) from (by
                                        unfold nb078AlphaDummy938;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0979 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                        (by
                                          unfold nb078AlphaDummy937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
                                          unfold nb078AlphaDummy938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy937), (nb078AlphaDummy938 h)),
                                      ((nb078AlphaDummy933), (nb078AlphaDummy935 h)),
                                      ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
                                      ((nb078AlphaDummy959), (nb078AlphaDummy960 h)),
                                      ((nb078AlphaDummy957), (nb078AlphaDummy958 h)),
                                      ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                      ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                      ((nb078AlphaDummy955), (nb078AlphaDummy956 h)),
                                      ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
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
                            (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy933) from (by
                                unfold nb078AlphaDummy933;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0976) 0))))
                            (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy935 h) from (by
                                unfold nb078AlphaDummy935;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0977 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy934) from (by
                                  unfold nb078AlphaDummy934;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0976) 1))))
                              (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy936 h) from
                                (by
                                  unfold nb078AlphaDummy936;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0977 h) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy959) from (by
                                    unfold nb078AlphaDummy959;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1006) 0)))) (show
                                  (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy960 h) from (by
                                    unfold nb078AlphaDummy960;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1007 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy957) from
                                    (by
                                      unfold nb078AlphaDummy957;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1004)
                                              0)))) (show
                                    (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy958 h) from
                                    (by
                                      unfold nb078AlphaDummy958;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1005 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy926))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy928 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy933) ≠ (nb078AlphaDummy940) from (by
          unfold nb078AlphaDummy940;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 1)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy943 h) from (by
          unfold nb078AlphaDummy943;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy933) ≠ (nb078AlphaDummy939) from (by
          unfold nb078AlphaDummy939;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy942 h) from (by
          unfold nb078AlphaDummy942;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937)
        from (by
          unfold nb078AlphaDummy937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978)
                  0)))) (show (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from (by
          unfold nb078AlphaDummy938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy941), (nb078AlphaDummy944 h)), ((nb078AlphaDummy940),
        (nb078AlphaDummy943 h)), ((nb078AlphaDummy939), (nb078AlphaDummy942 h)),
        ((nb078AlphaDummy937), (nb078AlphaDummy938 h)), ((nb078AlphaDummy933),
        (nb078AlphaDummy935 h)), ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
        ((nb078AlphaDummy959), (nb078AlphaDummy960 h)), ((nb078AlphaDummy957),
        (nb078AlphaDummy958 h)), ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
        ((nb078AlphaDummy925), (nb078AlphaDummy927 h)), ((nb078AlphaDummy955),
        (nb078AlphaDummy956 h)), ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy947) from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy947)
        from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy947) from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy947)
        from (by
          unfold
            nb078AlphaDummy947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy948 h) from (by
          unfold
            nb078AlphaDummy948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy945)
        from (by
          unfold
            nb078AlphaDummy945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy946 h) from (by
          unfold
            nb078AlphaDummy946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy941), (nb078AlphaDummy944 h)), ((nb078AlphaDummy940),
        (nb078AlphaDummy943 h)), ((nb078AlphaDummy939), (nb078AlphaDummy942 h)),
        ((nb078AlphaDummy937), (nb078AlphaDummy938 h)), ((nb078AlphaDummy933),
        (nb078AlphaDummy935 h)), ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
        ((nb078AlphaDummy959), (nb078AlphaDummy960 h)), ((nb078AlphaDummy957),
        (nb078AlphaDummy958 h)), ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
        ((nb078AlphaDummy925), (nb078AlphaDummy927 h)), ((nb078AlphaDummy955),
        (nb078AlphaDummy956 h)), ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy935
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy940) ≠
        (nb078AlphaDummy951) from (by
          unfold
            nb078AlphaDummy951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy952 h) from (by
          unfold
            nb078AlphaDummy952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy951)
        from (by
          unfold
            nb078AlphaDummy951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy952 h) from (by
          unfold
            nb078AlphaDummy952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078AlphaDummy943 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy953) from (by
          unfold
            nb078AlphaDummy953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy954 h) from (by
          unfold
            nb078AlphaDummy954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy941) ≠
        (nb078AlphaDummy953) from (by
          unfold
            nb078AlphaDummy953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy954 h) from (by
          unfold
            nb078AlphaDummy954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy941) ≠ (nb078AlphaDummy949)
        from (by
          unfold
            nb078AlphaDummy949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078AlphaDummy944 h) ≠ (nb078AlphaDummy950 h) from (by
          unfold
            nb078AlphaDummy950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                        (by
                                          unfold nb078AlphaDummy937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
                                          unfold nb078AlphaDummy938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy937), (nb078AlphaDummy938 h)),
                                      ((nb078AlphaDummy933), (nb078AlphaDummy935 h)),
                                      ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
                                      ((nb078AlphaDummy959), (nb078AlphaDummy960 h)),
                                      ((nb078AlphaDummy957), (nb078AlphaDummy958 h)),
                                      ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                      ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                      ((nb078AlphaDummy955), (nb078AlphaDummy956 h)),
                                      ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
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
                                      (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
                                        unfold nb078AlphaDummy937;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0978)
                                                0)))) (show (nb078AlphaDummy935 h) ≠
                                        (nb078AlphaDummy938 h) from (by
                                        unfold nb078AlphaDummy938;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0979 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                        (by
                                          unfold nb078AlphaDummy937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
                                          unfold nb078AlphaDummy938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy937), (nb078AlphaDummy938 h)),
                                      ((nb078AlphaDummy933), (nb078AlphaDummy935 h)),
                                      ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
                                      ((nb078AlphaDummy959), (nb078AlphaDummy960 h)),
                                      ((nb078AlphaDummy957), (nb078AlphaDummy958 h)),
                                      ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                      ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                      ((nb078AlphaDummy955), (nb078AlphaDummy956 h)),
                                      ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy957), (nb078AlphaDummy958 h)),
            ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
            ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
            ((nb078AlphaDummy955), (nb078AlphaDummy956 h)),
            ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
            ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
            ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
            ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
            ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part145`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0123`. -/
@[expose]
noncomputable def nb078SplitAlpha0123 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy966), (nb078AlphaDummy968 h)),
        ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy995), (nb078AlphaDummy996 h)),
        ((nb078AlphaDummy969), (nb078AlphaDummy970 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy966))
          (Class.cv (nb078AlphaDummy961))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy965))
            (synCun (synCphi (Class.cv (nb078AlphaDummy966))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy968 h))
          (Class.cv (nb078AlphaDummy963 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
            (synCun (synCphi (Class.cv (nb078AlphaDummy968 h))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy966) from (by
              unfold nb078AlphaDummy966;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))))
          (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy968 h) from (by
              unfold nb078AlphaDummy968;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))))
          (TAlphaVar.there (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy965) from (by
                unfold nb078AlphaDummy965;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))))
            (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy967 h) from (by
                unfold nb078AlphaDummy967;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))))
            (TAlphaVar.there (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy995) from (by
                  unfold nb078AlphaDummy995;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1040) 0))))
              (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy996 h) from (by
                  unfold nb078AlphaDummy996;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1041 h) 0))))
              (TAlphaVar.there (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy969) from (by
                    unfold nb078AlphaDummy969;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1037) 0))))
                (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy970 h) from (by
                    unfold nb078AlphaDummy970;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1039 h) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv)
                    (by decide))
                  (freshVar_injective (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078AlphaDummy962))).fv ∪
                ((Class.cv (nb078AlphaDummy961))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078AlphaDummy964 h))).fv ∪
                ((Class.cv (nb078AlphaDummy963 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy966) ≠ (nb078AlphaDummy973) from (by
                                        unfold nb078AlphaDummy973;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                0)))) (show (nb078AlphaDummy968 h) ≠
                                        (nb078AlphaDummy975 h) from (by
                                        unfold nb078AlphaDummy975;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy966) ≠ (nb078AlphaDummy974) from
                                        (by
                                          unfold nb078AlphaDummy974;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1014)
                                                  1)))) (show (nb078AlphaDummy968 h) ≠
        (nb078AlphaDummy976 h) from (by
                                          unfold nb078AlphaDummy976;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1015 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy966) ≠
        (nb078AlphaDummy999) from (by
          unfold nb078AlphaDummy999;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1044) 0)))) (show (nb078AlphaDummy968 h) ≠
        (nb078AlphaDummy1000 h) from (by
          unfold nb078AlphaDummy1000;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1045 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy966) ≠ (nb078AlphaDummy997) from (by
          unfold nb078AlphaDummy997;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1042) 0)))) (show (nb078AlphaDummy968 h) ≠
        (nb078AlphaDummy998 h) from (by
          unfold nb078AlphaDummy998;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1043 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy966))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy968 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy980) from (by
          unfold nb078AlphaDummy980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy983 h) from (by
          unfold nb078AlphaDummy983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy979)
        from (by
          unfold nb078AlphaDummy979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy982 h) from (by
          unfold nb078AlphaDummy982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977)
        from (by
          unfold
            nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy978 h) from (by
          unfold
            nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)), ((nb078AlphaDummy997),
        (nb078AlphaDummy998 h)), ((nb078AlphaDummy966), (nb078AlphaDummy968 h)),
        ((nb078AlphaDummy965), (nb078AlphaDummy967 h)), ((nb078AlphaDummy995),
        (nb078AlphaDummy996 h)), ((nb078AlphaDummy969), (nb078AlphaDummy970 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)), ((nb078AlphaDummy997),
        (nb078AlphaDummy998 h)), ((nb078AlphaDummy966), (nb078AlphaDummy968 h)),
        ((nb078AlphaDummy965), (nb078AlphaDummy967 h)), ((nb078AlphaDummy995),
        (nb078AlphaDummy996 h)), ((nb078AlphaDummy969), (nb078AlphaDummy970 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy973))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy980) ≠
        (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977)
        from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977), (nb078AlphaDummy978 h)),
        ((nb078AlphaDummy973), (nb078AlphaDummy975 h)), ((nb078AlphaDummy974),
        (nb078AlphaDummy976 h)), ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)),
        ((nb078AlphaDummy997), (nb078AlphaDummy998 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy995), (nb078AlphaDummy996 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977), (nb078AlphaDummy978 h)),
        ((nb078AlphaDummy973), (nb078AlphaDummy975 h)), ((nb078AlphaDummy974),
        (nb078AlphaDummy976 h)), ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)),
        ((nb078AlphaDummy997), (nb078AlphaDummy998 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy995), (nb078AlphaDummy996 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy966) ≠ (nb078AlphaDummy973) from (by
                                        unfold nb078AlphaDummy973;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                0)))) (show (nb078AlphaDummy968 h) ≠
                                        (nb078AlphaDummy975 h) from (by
                                        unfold nb078AlphaDummy975;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy966) ≠ (nb078AlphaDummy974) from
                                        (by
                                          unfold nb078AlphaDummy974;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1014)
                                                  1)))) (show (nb078AlphaDummy968 h) ≠
        (nb078AlphaDummy976 h) from (by
                                          unfold nb078AlphaDummy976;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1015 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy966) ≠
        (nb078AlphaDummy999) from (by
          unfold nb078AlphaDummy999;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1044) 0)))) (show (nb078AlphaDummy968 h) ≠
        (nb078AlphaDummy1000 h) from (by
          unfold nb078AlphaDummy1000;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1045 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy966) ≠ (nb078AlphaDummy997) from (by
          unfold nb078AlphaDummy997;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1042) 0)))) (show (nb078AlphaDummy968 h) ≠
        (nb078AlphaDummy998 h) from (by
          unfold nb078AlphaDummy998;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1043 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy966))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy968 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy980) from (by
          unfold nb078AlphaDummy980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy983 h) from (by
          unfold nb078AlphaDummy983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy979)
        from (by
          unfold nb078AlphaDummy979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy982 h) from (by
          unfold nb078AlphaDummy982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977)
        from (by
          unfold
            nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy978 h) from (by
          unfold
            nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)), ((nb078AlphaDummy997),
        (nb078AlphaDummy998 h)), ((nb078AlphaDummy966), (nb078AlphaDummy968 h)),
        ((nb078AlphaDummy965), (nb078AlphaDummy967 h)), ((nb078AlphaDummy995),
        (nb078AlphaDummy996 h)), ((nb078AlphaDummy969), (nb078AlphaDummy970 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)), ((nb078AlphaDummy997),
        (nb078AlphaDummy998 h)), ((nb078AlphaDummy966), (nb078AlphaDummy968 h)),
        ((nb078AlphaDummy965), (nb078AlphaDummy967 h)), ((nb078AlphaDummy995),
        (nb078AlphaDummy996 h)), ((nb078AlphaDummy969), (nb078AlphaDummy970 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy973))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy980) ≠
        (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977)
        from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977), (nb078AlphaDummy978 h)),
        ((nb078AlphaDummy973), (nb078AlphaDummy975 h)), ((nb078AlphaDummy974),
        (nb078AlphaDummy976 h)), ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)),
        ((nb078AlphaDummy997), (nb078AlphaDummy998 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy995), (nb078AlphaDummy996 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977), (nb078AlphaDummy978 h)),
        ((nb078AlphaDummy973), (nb078AlphaDummy975 h)), ((nb078AlphaDummy974),
        (nb078AlphaDummy976 h)), ((nb078AlphaDummy999), (nb078AlphaDummy1000 h)),
        ((nb078AlphaDummy997), (nb078AlphaDummy998 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy995), (nb078AlphaDummy996 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy997), (nb078AlphaDummy998 h)),
                    ((nb078AlphaDummy966), (nb078AlphaDummy968 h)),
                    ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
                    ((nb078AlphaDummy995), (nb078AlphaDummy996 h)),
                    ((nb078AlphaDummy969), (nb078AlphaDummy970 h)),
                    ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
                    ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part146`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0124`. -/
@[expose]
noncomputable def nb078SplitAlpha0124 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy969), (nb078AlphaDummy970 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy969)) (synCcompl
            (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCphi (Class.cv (nb078AlphaDummy966)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy969)) (synCcompl
              (Class.cab (nb078AlphaDummy965)
                (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
                  (Wff.classEq (Class.cv (nb078AlphaDummy965))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy970 h)) (synCcompl
            (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCphi (Class.cv (nb078AlphaDummy968 h)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy970 h)) (synCcompl
              (Class.cab (nb078AlphaDummy967 h)
                (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
                  (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy966) from (by
                              unfold nb078AlphaDummy966;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1008) 1))))
                          (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy968 h) from (by
                              unfold nb078AlphaDummy968;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy965) from (by
                                unfold nb078AlphaDummy965;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1008) 0))))
                            (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy967 h) from (by
                                unfold nb078AlphaDummy967;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy971) from (by
                                  unfold nb078AlphaDummy971;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1012) 0))))
                              (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy972 h) from
                                (by
                                  unfold nb078AlphaDummy972;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1013 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy969) from (by
                                    unfold nb078AlphaDummy969;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1009) 0)))) (show
                                  (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy970 h) from (by
                                    unfold nb078AlphaDummy970;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1011 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy962))).fv ∪
                              ((Class.cv (nb078AlphaDummy961))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy964 h))).fv ∪
                              ((Class.cv (nb078AlphaDummy963 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy966) ≠ (nb078AlphaDummy973) from
                                    (by
                                      unfold nb078AlphaDummy973;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1014)
                                              0)))) (show
                                    (nb078AlphaDummy968 h) ≠ (nb078AlphaDummy975 h) from
                                    (by
                                      unfold nb078AlphaDummy975;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1015 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy966) ≠ (nb078AlphaDummy974) from (by
                                        unfold nb078AlphaDummy974;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                1)))) (show (nb078AlphaDummy968 h) ≠
                                        (nb078AlphaDummy976 h) from (by
                                        unfold nb078AlphaDummy976;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy966))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy968 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy973) ≠ (nb078AlphaDummy980) from (by
          unfold nb078AlphaDummy980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy983 h) from (by
          unfold nb078AlphaDummy983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy979)
        from (by
          unfold nb078AlphaDummy979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy982 h) from (by
          unfold nb078AlphaDummy982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977)
        from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy966), (nb078AlphaDummy968 h)), ((nb078AlphaDummy965),
        (nb078AlphaDummy967 h)), ((nb078AlphaDummy971), (nb078AlphaDummy972 h)),
        ((nb078AlphaDummy969), (nb078AlphaDummy970 h)), ((nb078AlphaDummy962),
        (nb078AlphaDummy964 h)), ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy966), (nb078AlphaDummy968 h)), ((nb078AlphaDummy965),
        (nb078AlphaDummy967 h)), ((nb078AlphaDummy971), (nb078AlphaDummy972 h)),
        ((nb078AlphaDummy969), (nb078AlphaDummy970 h)), ((nb078AlphaDummy962),
        (nb078AlphaDummy964 h)), ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy973))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy980) ≠
        (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977),
        (nb078AlphaDummy978 h)), ((nb078AlphaDummy973), (nb078AlphaDummy975 h)),
        ((nb078AlphaDummy974), (nb078AlphaDummy976 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy971), (nb078AlphaDummy972 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy973) ≠
        (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977),
        (nb078AlphaDummy978 h)), ((nb078AlphaDummy973), (nb078AlphaDummy975 h)),
        ((nb078AlphaDummy974), (nb078AlphaDummy976 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy971), (nb078AlphaDummy972 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy966) from (by
                              unfold nb078AlphaDummy966;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1008) 1))))
                          (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy968 h) from (by
                              unfold nb078AlphaDummy968;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy965) from (by
                                unfold nb078AlphaDummy965;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1008) 0))))
                            (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy967 h) from (by
                                unfold nb078AlphaDummy967;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy971) from (by
                                  unfold nb078AlphaDummy971;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1012) 0))))
                              (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy972 h) from
                                (by
                                  unfold nb078AlphaDummy972;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1013 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy969) from (by
                                    unfold nb078AlphaDummy969;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1009) 0)))) (show
                                  (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy970 h) from (by
                                    unfold nb078AlphaDummy970;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1011 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy962))).fv ∪
                              ((Class.cv (nb078AlphaDummy961))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy964 h))).fv ∪
                              ((Class.cv (nb078AlphaDummy963 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy966) ≠ (nb078AlphaDummy973) from
                                    (by
                                      unfold nb078AlphaDummy973;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1014)
                                              0)))) (show
                                    (nb078AlphaDummy968 h) ≠ (nb078AlphaDummy975 h) from
                                    (by
                                      unfold nb078AlphaDummy975;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1015 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy966) ≠ (nb078AlphaDummy974) from (by
                                        unfold nb078AlphaDummy974;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                1)))) (show (nb078AlphaDummy968 h) ≠
                                        (nb078AlphaDummy976 h) from (by
                                        unfold nb078AlphaDummy976;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy966))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy968 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy973) ≠ (nb078AlphaDummy980) from (by
          unfold nb078AlphaDummy980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy983 h) from (by
          unfold nb078AlphaDummy983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy979)
        from (by
          unfold nb078AlphaDummy979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy982 h) from (by
          unfold nb078AlphaDummy982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy973) ≠ (nb078AlphaDummy977)
        from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078AlphaDummy975 h) ≠ (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy966), (nb078AlphaDummy968 h)), ((nb078AlphaDummy965),
        (nb078AlphaDummy967 h)), ((nb078AlphaDummy971), (nb078AlphaDummy972 h)),
        ((nb078AlphaDummy969), (nb078AlphaDummy970 h)), ((nb078AlphaDummy962),
        (nb078AlphaDummy964 h)), ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy987) from (by
          unfold
            nb078AlphaDummy987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy988 h) from (by
          unfold
            nb078AlphaDummy988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy985)
        from (by
          unfold
            nb078AlphaDummy985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy986 h) from (by
          unfold
            nb078AlphaDummy986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy981), (nb078AlphaDummy984 h)), ((nb078AlphaDummy980),
        (nb078AlphaDummy983 h)), ((nb078AlphaDummy979), (nb078AlphaDummy982 h)),
        ((nb078AlphaDummy977), (nb078AlphaDummy978 h)), ((nb078AlphaDummy973),
        (nb078AlphaDummy975 h)), ((nb078AlphaDummy974), (nb078AlphaDummy976 h)),
        ((nb078AlphaDummy966), (nb078AlphaDummy968 h)), ((nb078AlphaDummy965),
        (nb078AlphaDummy967 h)), ((nb078AlphaDummy971), (nb078AlphaDummy972 h)),
        ((nb078AlphaDummy969), (nb078AlphaDummy970 h)), ((nb078AlphaDummy962),
        (nb078AlphaDummy964 h)), ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy973))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy980) ≠
        (nb078AlphaDummy991) from (by
          unfold
            nb078AlphaDummy991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy992 h) from (by
          unfold
            nb078AlphaDummy992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy980) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078AlphaDummy983 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy975 h))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy981) ≠
        (nb078AlphaDummy993) from (by
          unfold
            nb078AlphaDummy993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy994 h) from (by
          unfold
            nb078AlphaDummy994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy981) ≠ (nb078AlphaDummy989)
        from (by
          unfold
            nb078AlphaDummy989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078AlphaDummy984 h) ≠ (nb078AlphaDummy990 h) from (by
          unfold
            nb078AlphaDummy990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977),
        (nb078AlphaDummy978 h)), ((nb078AlphaDummy973), (nb078AlphaDummy975 h)),
        ((nb078AlphaDummy974), (nb078AlphaDummy976 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy971), (nb078AlphaDummy972 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy973) ≠
        (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy973) ≠ (nb078AlphaDummy977) from (by
          unfold nb078AlphaDummy977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078AlphaDummy975 h) ≠
        (nb078AlphaDummy978 h) from (by
          unfold nb078AlphaDummy978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy977),
        (nb078AlphaDummy978 h)), ((nb078AlphaDummy973), (nb078AlphaDummy975 h)),
        ((nb078AlphaDummy974), (nb078AlphaDummy976 h)), ((nb078AlphaDummy966),
        (nb078AlphaDummy968 h)), ((nb078AlphaDummy965), (nb078AlphaDummy967 h)),
        ((nb078AlphaDummy971), (nb078AlphaDummy972 h)), ((nb078AlphaDummy969),
        (nb078AlphaDummy970 h)), ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0123 x y h)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0123 x y h)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
