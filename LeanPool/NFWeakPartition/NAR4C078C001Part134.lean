/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block044

/-! NF weak partition development: NAR4C078C001Part134. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0111`. -/
@[expose]
noncomputable def nb078SplitAlpha0111 (x : Var) (y : Var) (h : Var) :
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
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.classMem (Class.cv (nb078AlphaDummy957))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy926)))))
      (Wff.classMem (Class.cv (nb078AlphaDummy958 h))
        (synCcompl (synCphi (Class.cv (nb078AlphaDummy928 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
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
                          (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy936 h) from (by
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
                                      (mem_lt_freshVar (nb078_support_mem_1006) 0))))
                            (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy960 h) from (by
                                unfold nb078AlphaDummy960;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1007 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy957) from (by
                                  unfold nb078AlphaDummy957;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1004) 0))))
                              (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy958 h) from
                                (by
                                  unfold nb078AlphaDummy958;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1005 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy926))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy928 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy933) ≠
        (nb078AlphaDummy940) from (by
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
                  (nb078_support_mem_0981 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
          unfold nb078AlphaDummy937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978) 0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
          unfold nb078AlphaDummy938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy951) from (by
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
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                    (by
                                      unfold nb078AlphaDummy937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from
                                    (by
                                      unfold nb078AlphaDummy938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                  ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                  ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
                                    unfold nb078AlphaDummy937;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0978) 0)))) (show
                                  (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from (by
                                    unfold nb078AlphaDummy938;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0979 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                    (by
                                      unfold nb078AlphaDummy937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from
                                    (by
                                      unfold nb078AlphaDummy938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                  ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                  ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
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
                          (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy936 h) from (by
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
                                      (mem_lt_freshVar (nb078_support_mem_1006) 0))))
                            (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy960 h) from (by
                                unfold nb078AlphaDummy960;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1007 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy926) ≠ (nb078AlphaDummy957) from (by
                                  unfold nb078AlphaDummy957;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1004) 0))))
                              (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy958 h) from
                                (by
                                  unfold nb078AlphaDummy958;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1005 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078AlphaDummy926))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078AlphaDummy928 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy933) ≠
        (nb078AlphaDummy940) from (by
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
                  (nb078_support_mem_0981 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
          unfold nb078AlphaDummy937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978) 0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
          unfold nb078AlphaDummy938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
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
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy765),
        (nb078AlphaDummy766 h)), ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy940) ≠ (nb078AlphaDummy951) from (by
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
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                    (by
                                      unfold nb078AlphaDummy937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from
                                    (by
                                      unfold nb078AlphaDummy938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                  ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                  ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
                                    unfold nb078AlphaDummy937;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0978) 0)))) (show
                                  (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from (by
                                    unfold nb078AlphaDummy938;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0979 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                    (by
                                      unfold nb078AlphaDummy937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from
                                    (by
                                      unfold nb078AlphaDummy938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed
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
                                  ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                                  ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                                  ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                  ((nb078AlphaDummy003), x)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0112`. -/
@[expose]
noncomputable def nb078SplitAlpha0112 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
        ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy773))
          (synCop (Class.cv (nb078AlphaDummy767)) (Class.cv (nb078AlphaDummy768))))
        (Wff.neg (synWex (nb078AlphaDummy769) (synWa
              (synWbr (Class.cv (nb078AlphaDummy767))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy769))) (synWbr (Class.cv (nb078AlphaDummy769))
                (Class.cv (nb078AlphaDummy002)) (Class.cv (nb078AlphaDummy768)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy774 h))
          (synCop (Class.cv (nb078AlphaDummy770 h)) (Class.cv (nb078AlphaDummy771 h))))
        (Wff.neg (synWex (nb078AlphaDummy772 h) (synWa
              (synWbr (Class.cv (nb078AlphaDummy770 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy772 h)))
              (synWbr (Class.cv (nb078AlphaDummy772 h)) (Class.cv h)
                (Class.cv (nb078AlphaDummy771 h))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy773) from (by
                unfold nb078AlphaDummy773;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0800) 0))))) (Ne.symm
            (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy774 h) from (by
                unfold nb078AlphaDummy774;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0801 h) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy773) from
                (by
                  unfold nb078AlphaDummy773;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0798) 0)))))
            (Ne.symm (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy774 h) from (by
                  unfold nb078AlphaDummy774;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0799 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0102 x y h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy776) from
                                    (by
                                      unfold nb078AlphaDummy776;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0830)
                                              1)))) (show
                                    (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy778 h) from
                                    (by
                                      unfold nb078AlphaDummy778;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0832 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy768) ≠ (nb078AlphaDummy775) from (by
                                        unfold nb078AlphaDummy775;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0830)
                                                0)))) (show (nb078AlphaDummy771 h) ≠
                                        (nb078AlphaDummy777 h) from (by
                                        unfold nb078AlphaDummy777;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0832 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy768) ≠ (nb078AlphaDummy805) from
                                        (by
                                          unfold nb078AlphaDummy805;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0834)
                                                  0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy806 h) from (by
                                          unfold nb078AlphaDummy806;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0835 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy768) ≠
        (nb078AlphaDummy779) from (by
          unfold nb078AlphaDummy779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0831) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy780 h) from (by
          unfold nb078AlphaDummy780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0833 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy767))).fv ∪
                                      ((Class.cv (nb078AlphaDummy768))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy770 h))).fv ∪
                                      ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0103 x y h)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy776) from
                                    (by
                                      unfold nb078AlphaDummy776;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0830)
                                              1)))) (show
                                    (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy778 h) from
                                    (by
                                      unfold nb078AlphaDummy778;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0832 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy768) ≠ (nb078AlphaDummy775) from (by
                                        unfold nb078AlphaDummy775;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0830)
                                                0)))) (show (nb078AlphaDummy771 h) ≠
                                        (nb078AlphaDummy777 h) from (by
                                        unfold nb078AlphaDummy777;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0832 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy768) ≠ (nb078AlphaDummy805) from
                                        (by
                                          unfold nb078AlphaDummy805;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0834)
                                                  0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy806 h) from (by
                                          unfold nb078AlphaDummy806;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0835 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy768) ≠
        (nb078AlphaDummy779) from (by
          unfold nb078AlphaDummy779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0831) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy780 h) from (by
          unfold nb078AlphaDummy780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0833 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078AlphaDummy767))).fv ∪
                                      ((Class.cv (nb078AlphaDummy768))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy770 h))).fv ∪
                                      ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0103 x y h)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0104 x y h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy769) ≠
        (nb078AlphaDummy812) from (by
          unfold nb078AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 1)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy814 h) from (by
          unfold nb078AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy769) ≠ (nb078AlphaDummy811) from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 0)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy769) ≠ (nb078AlphaDummy841) from (by
          unfold nb078AlphaDummy841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872) 0)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy842 h) from (by
          unfold nb078AlphaDummy842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy769) ≠ (nb078AlphaDummy815) from (by
          unfold nb078AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869) 0)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy816 h) from (by
          unfold nb078AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy770 h))).fv ∪
        ((Class.cv (nb078AlphaDummy772 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0105 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy843), (nb078AlphaDummy844 h)), ((nb078AlphaDummy812),
        (nb078AlphaDummy814 h)), ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
        ((nb078AlphaDummy841), (nb078AlphaDummy842 h)), ((nb078AlphaDummy815),
        (nb078AlphaDummy816 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy769) ≠
        (nb078AlphaDummy812) from (by
          unfold nb078AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 1)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy814 h) from (by
          unfold nb078AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy769) ≠ (nb078AlphaDummy811) from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 0)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy769) ≠ (nb078AlphaDummy841) from (by
          unfold nb078AlphaDummy841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872) 0)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy842 h) from (by
          unfold nb078AlphaDummy842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy769) ≠ (nb078AlphaDummy815) from (by
          unfold nb078AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869) 0)))) (show (nb078AlphaDummy772 h) ≠
        (nb078AlphaDummy816 h) from (by
          unfold nb078AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy767))).fv ∪ ((Class.cv (nb078AlphaDummy769))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy770 h))).fv ∪
        ((Class.cv (nb078AlphaDummy772 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0105 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy843), (nb078AlphaDummy844 h)), ((nb078AlphaDummy812),
        (nb078AlphaDummy814 h)), ((nb078AlphaDummy811), (nb078AlphaDummy813 h)),
        ((nb078AlphaDummy841), (nb078AlphaDummy842 h)), ((nb078AlphaDummy815),
        (nb078AlphaDummy816 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy851) from (by
                                unfold nb078AlphaDummy851;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0880) 0))))) (Ne.symm
                            (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy852 h) from (by
                                unfold nb078AlphaDummy852;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0881 h) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy851) from (by
                                  unfold nb078AlphaDummy851;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0878) 0)))))
                            (Ne.symm (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy852 h)
                                from (by
                                  unfold nb078AlphaDummy852;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0879 h) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0106 x y h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy854) from (by
          unfold nb078AlphaDummy854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy856 h) from (by
          unfold nb078AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy853)
        from (by
          unfold nb078AlphaDummy853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold nb078AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy883)
        from (by
          unfold nb078AlphaDummy883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy884 h) from (by
          unfold nb078AlphaDummy884;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0915
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy857)
        from (by
          unfold nb078AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy858 h) from (by
          unfold nb078AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0913
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy847))).fv ∪
        ((Class.cv (nb078AlphaDummy848))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0107 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy854) from (by
          unfold nb078AlphaDummy854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy856 h) from (by
          unfold nb078AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy853)
        from (by
          unfold nb078AlphaDummy853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold nb078AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy883)
        from (by
          unfold nb078AlphaDummy883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy884 h) from (by
          unfold nb078AlphaDummy884;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0915
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy857)
        from (by
          unfold nb078AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy858 h) from (by
          unfold nb078AlphaDummy858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0913
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy847))).fv ∪
        ((Class.cv (nb078AlphaDummy848))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0107 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0108 x y h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy890) from (by
          unfold nb078AlphaDummy890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy892 h) from (by
          unfold nb078AlphaDummy892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy889)
        from (by
          unfold nb078AlphaDummy889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold nb078AlphaDummy891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy919)
        from (by
          unfold nb078AlphaDummy919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy920 h) from (by
          unfold nb078AlphaDummy920;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0953
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy893)
        from (by
          unfold nb078AlphaDummy893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy894 h) from (by
          unfold nb078AlphaDummy894;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0951
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy002))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy848))).fv ∪
        ((Class.cv (nb078AlphaDummy847))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0109 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy890) from (by
          unfold nb078AlphaDummy890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy892 h) from (by
          unfold nb078AlphaDummy892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy889)
        from (by
          unfold nb078AlphaDummy889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold nb078AlphaDummy891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy919)
        from (by
          unfold nb078AlphaDummy919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy920 h) from (by
          unfold nb078AlphaDummy920;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0953
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy893)
        from (by
          unfold nb078AlphaDummy893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy894 h) from (by
          unfold nb078AlphaDummy894;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0951
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy002))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy848))).fv ∪
        ((Class.cv (nb078AlphaDummy847))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0109 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy848) from (by
                              unfold nb078AlphaDummy848;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0968) 1))))
                          (show h ≠ (nb078AlphaDummy850 h) from (by
                              unfold nb078AlphaDummy850;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0969 h) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy847) from (by
                                unfold nb078AlphaDummy847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0968) 0))))
                            (show h ≠ (nb078AlphaDummy849 h) from (by
                                unfold nb078AlphaDummy849;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0969 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy851) from (by
                                  unfold nb078AlphaDummy851;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0966) 0))))
                              (show h ≠ (nb078AlphaDummy852 h) from (by
                                  unfold nb078AlphaDummy852;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0967 h) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy769) from (by
                                    unfold nb078AlphaDummy769;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0962) 2))))
                                (show h ≠ (nb078AlphaDummy772 h) from (by
                                    unfold nb078AlphaDummy772;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0964 h)
                                            2)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy768) from
                                    (by
                                      unfold nb078AlphaDummy768;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0962)
                                              1)))) (show h ≠ (nb078AlphaDummy771 h) from (by
                                      unfold nb078AlphaDummy771;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0964 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy002) ≠ (nb078AlphaDummy767) from (by
                                        unfold nb078AlphaDummy767;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0962)
                                                0)))) (show h ≠ (nb078AlphaDummy770 h) from
                                      (by
                                        unfold nb078AlphaDummy770;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0964 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy002) ≠ (nb078AlphaDummy773) from
                                        (by
                                          unfold nb078AlphaDummy773;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0963)
                                                  0)))) (show h ≠ (nb078AlphaDummy774 h) from
                                        (by
                                          unfold nb078AlphaDummy774;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0965 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy002) ≠
        (nb078AlphaDummy765) from (by
          unfold nb078AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0960) 0)))) (show h ≠ (nb078AlphaDummy766 h) from (by
          unfold nb078AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0961 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy763) from (by
          unfold nb078AlphaDummy763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0958) 0)))) (show h ≠ (nb078AlphaDummy764 h) from (by
          unfold nb078AlphaDummy764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0959 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0110 x y h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy768) ≠
        (nb078AlphaDummy926) from (by
          unfold nb078AlphaDummy926;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 1)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy928 h) from (by
          unfold nb078AlphaDummy928;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy768) ≠ (nb078AlphaDummy925) from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy768) ≠ (nb078AlphaDummy955) from (by
          unfold nb078AlphaDummy955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy956 h) from (by
          unfold nb078AlphaDummy956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy768) ≠ (nb078AlphaDummy929) from (by
          unfold nb078AlphaDummy929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy930 h) from (by
          unfold nb078AlphaDummy930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCcnv (Class.cv
        (nb078AlphaDummy002)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy772 h))).fv ∪
        ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0111 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy957), (nb078AlphaDummy958 h)), ((nb078AlphaDummy926),
        (nb078AlphaDummy928 h)), ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
        ((nb078AlphaDummy955), (nb078AlphaDummy956 h)), ((nb078AlphaDummy929),
        (nb078AlphaDummy930 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy768) ≠
        (nb078AlphaDummy926) from (by
          unfold nb078AlphaDummy926;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 1)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy928 h) from (by
          unfold nb078AlphaDummy928;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy768) ≠ (nb078AlphaDummy925) from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy768) ≠ (nb078AlphaDummy955) from (by
          unfold nb078AlphaDummy955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy956 h) from (by
          unfold nb078AlphaDummy956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy768) ≠ (nb078AlphaDummy929) from (by
          unfold nb078AlphaDummy929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999) 0)))) (show (nb078AlphaDummy771 h) ≠
        (nb078AlphaDummy930 h) from (by
          unfold nb078AlphaDummy930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCcnv (Class.cv
        (nb078AlphaDummy002)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy772 h))).fv ∪
        ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078SplitAlpha0111 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy957), (nb078AlphaDummy958 h)), ((nb078AlphaDummy926),
        (nb078AlphaDummy928 h)), ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
        ((nb078AlphaDummy955), (nb078AlphaDummy956 h)), ((nb078AlphaDummy929),
        (nb078AlphaDummy930 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy765), (nb078AlphaDummy766 h)), ((nb078AlphaDummy763),
        (nb078AlphaDummy764 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy769) from (by
                    unfold nb078AlphaDummy769;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 2))))
                (show h ≠ (nb078AlphaDummy772 h) from (by
                    unfold nb078AlphaDummy772;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0964 h) 2))))
                (TAlphaVar.there (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy768) from
                    (by
                      unfold nb078AlphaDummy768;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 1))))
                  (show h ≠ (nb078AlphaDummy771 h) from (by
                      unfold nb078AlphaDummy771;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0964 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy767) from
                      (by
                        unfold nb078AlphaDummy767;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 0))))
                    (show h ≠ (nb078AlphaDummy770 h) from (by
                        unfold nb078AlphaDummy770;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0964 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy773) from (by
                          unfold nb078AlphaDummy773;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0963) 0))))
                      (show h ≠ (nb078AlphaDummy774 h) from (by
                          unfold nb078AlphaDummy774;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0965 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy765) from (by
                            unfold nb078AlphaDummy765;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0960) 0))))
                        (show h ≠ (nb078AlphaDummy766 h) from (by
                            unfold nb078AlphaDummy766;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0961 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy763) from (by
                              unfold nb078AlphaDummy763;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0958) 0))))
                          (show h ≠ (nb078AlphaDummy764 h) from (by
                              unfold nb078AlphaDummy764;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0959 h) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb078_wpp_notmem_2424 : (nb078AlphaDummy765) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy765, fv_syn_cid] using (nb078_compact_fv_empty_0602)

theorem nb078_wpp_notmem_2425 (h : Var) : (nb078AlphaDummy766 h) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy766, fv_syn_cid] using (nb078_compact_fv_empty_0603 h)

theorem nb078_wpp_notmem_2426 : (nb078AlphaDummy763) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy763, fv_syn_cid] using (nb078_compact_fv_empty_0604)

theorem nb078_wpp_notmem_2427 (h : Var) : (nb078AlphaDummy764 h) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy764, fv_syn_cid] using (nb078_compact_fv_empty_0605 h)

theorem nb078_wpp_notmem_2428 : (nb078AlphaDummy002) ∉ ((synCid)).fv := by
  simpa only [nb078AlphaDummy002, fv_syn_cid] using (nb078_compact_fv_empty_0606)

theorem nb078_wpp_notmem_2429 (h : Var) : h ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0607 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
