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

@[expose]
noncomputable def nb078_split_alpha_0111 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)),
        ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
        ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
        ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)),
        ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
        ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.classMem (Class.cv (nb078_alpha_dummy_957))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))
      (Wff.classMem (Class.cv (nb078_alpha_dummy_958 h))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_933) from (by
                            unfold nb078_alpha_dummy_933;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0976) 0))))
                        (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_935 h) from (by
                            unfold nb078_alpha_dummy_935;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0977 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_934) from (by
                              unfold nb078_alpha_dummy_934;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0976) 1))))
                          (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_936 h) from (by
                              unfold nb078_alpha_dummy_936;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0977 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_959) from (by
                                unfold nb078_alpha_dummy_959;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1006) 0))))
                            (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_960 h) from (by
                                unfold nb078_alpha_dummy_960;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1007 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_957) from (by
                                  unfold nb078_alpha_dummy_957;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1004) 0))))
                              (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_958 h) from
                                (by
                                  unfold nb078_alpha_dummy_958;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1005 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_928 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_933) ≠
        (nb078_alpha_dummy_940) from (by
          unfold nb078_alpha_dummy_940;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 1)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_943 h) from (by
          unfold nb078_alpha_dummy_943;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_939) from (by
          unfold nb078_alpha_dummy_939;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_942 h) from (by
          unfold nb078_alpha_dummy_942;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from (by
          unfold nb078_alpha_dummy_937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978) 0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_938 h) from (by
          unfold nb078_alpha_dummy_938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940),
        (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)),
        ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933),
        (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
        ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957),
        (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
        ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955),
        (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765),
        (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_947) from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_947)
        from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_947) from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_947)
        from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940),
        (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)),
        ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933),
        (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
        ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957),
        (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
        ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955),
        (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765),
        (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_951) from (by
          unfold
            nb078_alpha_dummy_951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_952 h) from (by
          unfold
            nb078_alpha_dummy_952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_951)
        from (by
          unfold
            nb078_alpha_dummy_951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_952 h) from (by
          unfold
            nb078_alpha_dummy_952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_953) from (by
          unfold
            nb078_alpha_dummy_953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_954 h) from (by
          unfold
            nb078_alpha_dummy_954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠
        (nb078_alpha_dummy_953) from (by
          unfold
            nb078_alpha_dummy_953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_954 h) from (by
          unfold
            nb078_alpha_dummy_954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                    (by
                                      unfold nb078_alpha_dummy_937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from
                                    (by
                                      unfold nb078_alpha_dummy_938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)),
                                  ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)),
                                  ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
                                  ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)),
                                  ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)),
                                  ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                  ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                  ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)),
                                  ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
                                  ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                  ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                  ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                  ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                  ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
                                  ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
                                  ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from (by
                                    unfold nb078_alpha_dummy_937;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0978) 0)))) (show
                                  (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from (by
                                    unfold nb078_alpha_dummy_938;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0979 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                    (by
                                      unfold nb078_alpha_dummy_937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from
                                    (by
                                      unfold nb078_alpha_dummy_938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)),
                                  ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)),
                                  ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
                                  ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)),
                                  ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)),
                                  ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                  ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                  ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)),
                                  ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
                                  ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                  ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                  ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                  ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                  ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
                                  ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
                                  ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_933) from (by
                            unfold nb078_alpha_dummy_933;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0976) 0))))
                        (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_935 h) from (by
                            unfold nb078_alpha_dummy_935;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0977 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_934) from (by
                              unfold nb078_alpha_dummy_934;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0976) 1))))
                          (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_936 h) from (by
                              unfold nb078_alpha_dummy_936;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0977 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_959) from (by
                                unfold nb078_alpha_dummy_959;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1006) 0))))
                            (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_960 h) from (by
                                unfold nb078_alpha_dummy_960;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1007 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_957) from (by
                                  unfold nb078_alpha_dummy_957;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1004) 0))))
                              (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_958 h) from
                                (by
                                  unfold nb078_alpha_dummy_958;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1005 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_928 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_933) ≠
        (nb078_alpha_dummy_940) from (by
          unfold nb078_alpha_dummy_940;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 1)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_943 h) from (by
          unfold nb078_alpha_dummy_943;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_939) from (by
          unfold nb078_alpha_dummy_939;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0980) 0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_942 h) from (by
          unfold nb078_alpha_dummy_942;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0981 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from (by
          unfold nb078_alpha_dummy_937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978) 0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_938 h) from (by
          unfold nb078_alpha_dummy_938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940),
        (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)),
        ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933),
        (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
        ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957),
        (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
        ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955),
        (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765),
        (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_947) from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_947)
        from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_947) from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0984)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0985
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0982)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0983
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_947)
        from (by
          unfold
            nb078_alpha_dummy_947;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0988)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_948 h) from (by
          unfold
            nb078_alpha_dummy_948;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0989
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_945)
        from (by
          unfold
            nb078_alpha_dummy_945;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0986)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_946 h) from (by
          unfold
            nb078_alpha_dummy_946;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0987
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940),
        (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)),
        ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933),
        (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
        ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957),
        (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
        ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955),
        (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765),
        (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_951) from (by
          unfold
            nb078_alpha_dummy_951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_952 h) from (by
          unfold
            nb078_alpha_dummy_952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_951)
        from (by
          unfold
            nb078_alpha_dummy_951;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0992)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_952 h) from (by
          unfold
            nb078_alpha_dummy_952;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0993
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0990)
                  0)))) (show (nb078_alpha_dummy_943 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0991
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_953) from (by
          unfold
            nb078_alpha_dummy_953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_954 h) from (by
          unfold
            nb078_alpha_dummy_954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠
        (nb078_alpha_dummy_953) from (by
          unfold
            nb078_alpha_dummy_953;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0996)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_954 h) from (by
          unfold
            nb078_alpha_dummy_954;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0997
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_941) ≠ (nb078_alpha_dummy_949)
        from (by
          unfold
            nb078_alpha_dummy_949;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0994)
                  0)))) (show (nb078_alpha_dummy_944 h) ≠ (nb078_alpha_dummy_950 h) from (by
          unfold
            nb078_alpha_dummy_950;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0995
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                    (by
                                      unfold nb078_alpha_dummy_937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from
                                    (by
                                      unfold nb078_alpha_dummy_938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)),
                                  ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)),
                                  ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
                                  ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)),
                                  ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)),
                                  ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                  ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                  ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)),
                                  ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
                                  ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                  ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                  ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                  ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                  ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
                                  ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
                                  ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from (by
                                    unfold nb078_alpha_dummy_937;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0978) 0)))) (show
                                  (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from (by
                                    unfold nb078_alpha_dummy_938;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0979 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                    (by
                                      unfold nb078_alpha_dummy_937;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0978)
                                              0)))) (show
                                    (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from
                                    (by
                                      unfold nb078_alpha_dummy_938;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0979 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)),
                                  ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)),
                                  ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
                                  ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)),
                                  ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)),
                                  ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                  ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                  ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)),
                                  ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
                                  ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                  ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                  ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                  ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                  ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
                                  ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
                                  ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

@[expose]
noncomputable def nb078_split_alpha_0112 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
        ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_773))
          (syn_cop (Class.cv (nb078_alpha_dummy_767)) (Class.cv (nb078_alpha_dummy_768))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_769) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_767))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769))
                (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_774 h))
          (syn_cop (Class.cv (nb078_alpha_dummy_770 h)) (Class.cv (nb078_alpha_dummy_771 h))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_772 h) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_772 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h)
                (Class.cv (nb078_alpha_dummy_771 h))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_773) from (by
                unfold nb078_alpha_dummy_773;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0800) 0))))) (Ne.symm
            (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_774 h) from (by
                unfold nb078_alpha_dummy_774;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0801 h) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_773) from
                (by
                  unfold nb078_alpha_dummy_773;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0798) 0)))))
            (Ne.symm (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_774 h) from (by
                  unfold nb078_alpha_dummy_774;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0799 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0102 x y h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_776) from
                                    (by
                                      unfold nb078_alpha_dummy_776;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0830)
                                              1)))) (show
                                    (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_778 h) from
                                    (by
                                      unfold nb078_alpha_dummy_778;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0832 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_775) from (by
                                        unfold nb078_alpha_dummy_775;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0830)
                                                0)))) (show (nb078_alpha_dummy_771 h) ≠
                                        (nb078_alpha_dummy_777 h) from (by
                                        unfold nb078_alpha_dummy_777;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0832 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_805) from
                                        (by
                                          unfold nb078_alpha_dummy_805;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0834)
                                                  0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_806 h) from (by
                                          unfold nb078_alpha_dummy_806;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0835 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠
        (nb078_alpha_dummy_779) from (by
          unfold nb078_alpha_dummy_779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0831) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_780 h) from (by
          unfold nb078_alpha_dummy_780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0833 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0103 x y h)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_776) from
                                    (by
                                      unfold nb078_alpha_dummy_776;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0830)
                                              1)))) (show
                                    (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_778 h) from
                                    (by
                                      unfold nb078_alpha_dummy_778;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0832 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_775) from (by
                                        unfold nb078_alpha_dummy_775;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0830)
                                                0)))) (show (nb078_alpha_dummy_771 h) ≠
                                        (nb078_alpha_dummy_777 h) from (by
                                        unfold nb078_alpha_dummy_777;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0832 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_805) from
                                        (by
                                          unfold nb078_alpha_dummy_805;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0834)
                                                  0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_806 h) from (by
                                          unfold nb078_alpha_dummy_806;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0835 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠
        (nb078_alpha_dummy_779) from (by
          unfold nb078_alpha_dummy_779;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0831) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_780 h) from (by
          unfold nb078_alpha_dummy_780;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0833 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0103 x y h)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0104 x y h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠
        (nb078_alpha_dummy_812) from (by
          unfold nb078_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 1)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_814 h) from (by
          unfold nb078_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_811) from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 0)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_841) from (by
          unfold nb078_alpha_dummy_841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872) 0)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_842 h) from (by
          unfold nb078_alpha_dummy_842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_815) from (by
          unfold nb078_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869) 0)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_816 h) from (by
          unfold nb078_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_772 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0105 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812),
        (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
        ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815),
        (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠
        (nb078_alpha_dummy_812) from (by
          unfold nb078_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 1)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_814 h) from (by
          unfold nb078_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_811) from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868) 0)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_841) from (by
          unfold nb078_alpha_dummy_841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872) 0)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_842 h) from (by
          unfold nb078_alpha_dummy_842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_815) from (by
          unfold nb078_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869) 0)))) (show (nb078_alpha_dummy_772 h) ≠
        (nb078_alpha_dummy_816 h) from (by
          unfold nb078_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_769))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_772 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0105 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812),
        (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
        ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815),
        (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_851) from (by
                                unfold nb078_alpha_dummy_851;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0880) 0))))) (Ne.symm
                            (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_852 h) from (by
                                unfold nb078_alpha_dummy_852;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0881 h) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_851) from (by
                                  unfold nb078_alpha_dummy_851;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0878) 0)))))
                            (Ne.symm (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_852 h)
                                from (by
                                  unfold nb078_alpha_dummy_852;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0879 h) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0106 x y h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_854) from (by
          unfold nb078_alpha_dummy_854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_856 h) from (by
          unfold nb078_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853)
        from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold nb078_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_883)
        from (by
          unfold nb078_alpha_dummy_883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_884 h) from (by
          unfold nb078_alpha_dummy_884;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0915
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_857)
        from (by
          unfold nb078_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_858 h) from (by
          unfold nb078_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0913
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_847))).fv ∪
        ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0107 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_854) from (by
          unfold nb078_alpha_dummy_854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_856 h) from (by
          unfold nb078_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853)
        from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold nb078_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_883)
        from (by
          unfold nb078_alpha_dummy_883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_884 h) from (by
          unfold nb078_alpha_dummy_884;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0915
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_857)
        from (by
          unfold nb078_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_858 h) from (by
          unfold nb078_alpha_dummy_858;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0913
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_847))).fv ∪
        ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0107 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0108 x y h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_890) from (by
          unfold nb078_alpha_dummy_890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_892 h) from (by
          unfold nb078_alpha_dummy_892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889)
        from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold nb078_alpha_dummy_891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_919)
        from (by
          unfold nb078_alpha_dummy_919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_920 h) from (by
          unfold nb078_alpha_dummy_920;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0953
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_893)
        from (by
          unfold nb078_alpha_dummy_893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_894 h) from (by
          unfold nb078_alpha_dummy_894;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0951
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_848))).fv ∪
        ((Class.cv (nb078_alpha_dummy_847))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0109 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_890) from (by
          unfold nb078_alpha_dummy_890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_892 h) from (by
          unfold nb078_alpha_dummy_892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889)
        from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold nb078_alpha_dummy_891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_919)
        from (by
          unfold nb078_alpha_dummy_919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_920 h) from (by
          unfold nb078_alpha_dummy_920;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0953
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_893)
        from (by
          unfold nb078_alpha_dummy_893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_894 h) from (by
          unfold nb078_alpha_dummy_894;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0951
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_848))).fv ∪
        ((Class.cv (nb078_alpha_dummy_847))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0109 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_848) from (by
                              unfold nb078_alpha_dummy_848;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0968) 1))))
                          (show h ≠ (nb078_alpha_dummy_850 h) from (by
                              unfold nb078_alpha_dummy_850;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0969 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_847) from (by
                                unfold nb078_alpha_dummy_847;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0968) 0))))
                            (show h ≠ (nb078_alpha_dummy_849 h) from (by
                                unfold nb078_alpha_dummy_849;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0969 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_851) from (by
                                  unfold nb078_alpha_dummy_851;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0966) 0))))
                              (show h ≠ (nb078_alpha_dummy_852 h) from (by
                                  unfold nb078_alpha_dummy_852;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0967 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_769) from (by
                                    unfold nb078_alpha_dummy_769;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0962) 2))))
                                (show h ≠ (nb078_alpha_dummy_772 h) from (by
                                    unfold nb078_alpha_dummy_772;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0964 h)
                                            2)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_768) from
                                    (by
                                      unfold nb078_alpha_dummy_768;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0962)
                                              1)))) (show h ≠ (nb078_alpha_dummy_771 h) from (by
                                      unfold nb078_alpha_dummy_771;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0964 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_767) from (by
                                        unfold nb078_alpha_dummy_767;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0962)
                                                0)))) (show h ≠ (nb078_alpha_dummy_770 h) from
                                      (by
                                        unfold nb078_alpha_dummy_770;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0964 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_773) from
                                        (by
                                          unfold nb078_alpha_dummy_773;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0963)
                                                  0)))) (show h ≠ (nb078_alpha_dummy_774 h) from
                                        (by
                                          unfold nb078_alpha_dummy_774;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0965 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠
        (nb078_alpha_dummy_765) from (by
          unfold nb078_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0960) 0)))) (show h ≠ (nb078_alpha_dummy_766 h) from (by
          unfold nb078_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0961 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_763) from (by
          unfold nb078_alpha_dummy_763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0958) 0)))) (show h ≠ (nb078_alpha_dummy_764 h) from (by
          unfold nb078_alpha_dummy_764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0959 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0110 x y h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠
        (nb078_alpha_dummy_926) from (by
          unfold nb078_alpha_dummy_926;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 1)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_928 h) from (by
          unfold nb078_alpha_dummy_928;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_925) from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_955) from (by
          unfold nb078_alpha_dummy_955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_956 h) from (by
          unfold nb078_alpha_dummy_956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_929) from (by
          unfold nb078_alpha_dummy_929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_930 h) from (by
          unfold nb078_alpha_dummy_930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv
        (nb078_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0111 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926),
        (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
        ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929),
        (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠
        (nb078_alpha_dummy_926) from (by
          unfold nb078_alpha_dummy_926;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 1)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_928 h) from (by
          unfold nb078_alpha_dummy_928;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_925) from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_955) from (by
          unfold nb078_alpha_dummy_955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_956 h) from (by
          unfold nb078_alpha_dummy_956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_929) from (by
          unfold nb078_alpha_dummy_929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999) 0)))) (show (nb078_alpha_dummy_771 h) ≠
        (nb078_alpha_dummy_930 h) from (by
          unfold nb078_alpha_dummy_930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv
        (nb078_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0111 x y h)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926),
        (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
        ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929),
        (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763),
        (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_769) from (by
                    unfold nb078_alpha_dummy_769;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 2))))
                (show h ≠ (nb078_alpha_dummy_772 h) from (by
                    unfold nb078_alpha_dummy_772;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0964 h) 2))))
                (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_768) from
                    (by
                      unfold nb078_alpha_dummy_768;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 1))))
                  (show h ≠ (nb078_alpha_dummy_771 h) from (by
                      unfold nb078_alpha_dummy_771;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0964 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_767) from
                      (by
                        unfold nb078_alpha_dummy_767;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 0))))
                    (show h ≠ (nb078_alpha_dummy_770 h) from (by
                        unfold nb078_alpha_dummy_770;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0964 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_773) from (by
                          unfold nb078_alpha_dummy_773;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0963) 0))))
                      (show h ≠ (nb078_alpha_dummy_774 h) from (by
                          unfold nb078_alpha_dummy_774;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0965 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_765) from (by
                            unfold nb078_alpha_dummy_765;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0960) 0))))
                        (show h ≠ (nb078_alpha_dummy_766 h) from (by
                            unfold nb078_alpha_dummy_766;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0961 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_763) from (by
                              unfold nb078_alpha_dummy_763;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0958) 0))))
                          (show h ≠ (nb078_alpha_dummy_764 h) from (by
                              unfold nb078_alpha_dummy_764;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0959 h) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb078_wpp_notmem_2424 : (nb078_alpha_dummy_765) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_765, fv_syn_cid] using (nb078_compact_fv_empty_0602)

theorem nb078_wpp_notmem_2425 (h : Var) : (nb078_alpha_dummy_766 h) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_766, fv_syn_cid] using (nb078_compact_fv_empty_0603 h)

theorem nb078_wpp_notmem_2426 : (nb078_alpha_dummy_763) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_763, fv_syn_cid] using (nb078_compact_fv_empty_0604)

theorem nb078_wpp_notmem_2427 (h : Var) : (nb078_alpha_dummy_764 h) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_764, fv_syn_cid] using (nb078_compact_fv_empty_0605 h)

theorem nb078_wpp_notmem_2428 : (nb078_alpha_dummy_002) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_002, fv_syn_cid] using (nb078_compact_fv_empty_0606)

theorem nb078_wpp_notmem_2429 (h : Var) : h ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0607 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
