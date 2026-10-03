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

@[expose]
noncomputable def nb078_split_alpha_0122 (x : Var) (y : Var) (h : Var) :
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
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_957))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_957)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_958 h))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_958 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_936 h) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_1006) 0)))) (show
                                  (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_960 h) from (by
                                    unfold nb078_alpha_dummy_960;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1007 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_957) from
                                    (by
                                      unfold nb078_alpha_dummy_957;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1004)
                                              0)))) (show
                                    (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_958 h) from
                                    (by
                                      unfold nb078_alpha_dummy_958;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1005 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_928 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_940) from (by
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
                  (nb078_support_mem_0981 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937)
        from (by
          unfold nb078_alpha_dummy_937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978)
                  0)))) (show (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from (by
          unfold nb078_alpha_dummy_938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
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
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠
        (nb078_alpha_dummy_951) from (by
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                        (by
                                          unfold nb078_alpha_dummy_937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_938 h) from (by
                                          unfold nb078_alpha_dummy_938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from (by
                                        unfold nb078_alpha_dummy_937;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0978)
                                                0)))) (show (nb078_alpha_dummy_935 h) ≠
                                        (nb078_alpha_dummy_938 h) from (by
                                        unfold nb078_alpha_dummy_938;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0979 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                        (by
                                          unfold nb078_alpha_dummy_937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_938 h) from (by
                                          unfold nb078_alpha_dummy_938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_936 h) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_1006) 0)))) (show
                                  (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_960 h) from (by
                                    unfold nb078_alpha_dummy_960;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1007 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_926) ≠ (nb078_alpha_dummy_957) from
                                    (by
                                      unfold nb078_alpha_dummy_957;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1004)
                                              0)))) (show
                                    (nb078_alpha_dummy_928 h) ≠ (nb078_alpha_dummy_958 h) from
                                    (by
                                      unfold nb078_alpha_dummy_958;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1005 h)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_928 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_940) from (by
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
                  (nb078_support_mem_0981 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937)
        from (by
          unfold nb078_alpha_dummy_937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978)
                  0)))) (show (nb078_alpha_dummy_935 h) ≠ (nb078_alpha_dummy_938 h) from (by
          unfold nb078_alpha_dummy_938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
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
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_940) ≠
        (nb078_alpha_dummy_951) from (by
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                        (by
                                          unfold nb078_alpha_dummy_937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_938 h) from (by
                                          unfold nb078_alpha_dummy_938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from (by
                                        unfold nb078_alpha_dummy_937;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0978)
                                                0)))) (show (nb078_alpha_dummy_935 h) ≠
                                        (nb078_alpha_dummy_938 h) from (by
                                        unfold nb078_alpha_dummy_938;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0979 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_937) from
                                        (by
                                          unfold nb078_alpha_dummy_937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078_alpha_dummy_935 h) ≠
        (nb078_alpha_dummy_938 h) from (by
                                          unfold nb078_alpha_dummy_938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
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
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)),
            ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
            ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
            ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)),
            ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
            ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
            ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
            ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
            ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
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

@[expose]
noncomputable def nb078_split_alpha_0123 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)),
        ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)),
        ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_966))
          (Class.cv (nb078_alpha_dummy_961))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_968 h))
          (Class.cv (nb078_alpha_dummy_963 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_966) from (by
              unfold nb078_alpha_dummy_966;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))))
          (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_968 h) from (by
              unfold nb078_alpha_dummy_968;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_965) from (by
                unfold nb078_alpha_dummy_965;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))))
            (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_967 h) from (by
                unfold nb078_alpha_dummy_967;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_995) from (by
                  unfold nb078_alpha_dummy_995;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1040) 0))))
              (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_996 h) from (by
                  unfold nb078_alpha_dummy_996;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1041 h) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_969) from (by
                    unfold nb078_alpha_dummy_969;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1037) 0))))
                (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_970 h) from (by
                    unfold nb078_alpha_dummy_970;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1039 h) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv)
                    (by decide))
                  (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_962))).fv ∪
                ((Class.cv (nb078_alpha_dummy_961))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪
                ((Class.cv (nb078_alpha_dummy_963 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_973) from (by
                                        unfold nb078_alpha_dummy_973;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                0)))) (show (nb078_alpha_dummy_968 h) ≠
                                        (nb078_alpha_dummy_975 h) from (by
                                        unfold nb078_alpha_dummy_975;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_974) from
                                        (by
                                          unfold nb078_alpha_dummy_974;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1014)
                                                  1)))) (show (nb078_alpha_dummy_968 h) ≠
        (nb078_alpha_dummy_976 h) from (by
                                          unfold nb078_alpha_dummy_976;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1015 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_966) ≠
        (nb078_alpha_dummy_999) from (by
          unfold nb078_alpha_dummy_999;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1044) 0)))) (show (nb078_alpha_dummy_968 h) ≠
        (nb078_alpha_dummy_1000 h) from (by
          unfold nb078_alpha_dummy_1000;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1045 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_997) from (by
          unfold nb078_alpha_dummy_997;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1042) 0)))) (show (nb078_alpha_dummy_968 h) ≠
        (nb078_alpha_dummy_998 h) from (by
          unfold nb078_alpha_dummy_998;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1043 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_966))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_968 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_980) from (by
          unfold nb078_alpha_dummy_980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_983 h) from (by
          unfold nb078_alpha_dummy_983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_979)
        from (by
          unfold nb078_alpha_dummy_979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_982 h) from (by
          unfold nb078_alpha_dummy_982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977)
        from (by
          unfold
            nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_978 h) from (by
          unfold
            nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)), ((nb078_alpha_dummy_997),
        (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)),
        ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_995),
        (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)), ((nb078_alpha_dummy_997),
        (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)),
        ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_995),
        (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠
        (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977)
        from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)),
        ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974),
        (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)),
        ((nb078_alpha_dummy_997), (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)),
        ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974),
        (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)),
        ((nb078_alpha_dummy_997), (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_973) from (by
                                        unfold nb078_alpha_dummy_973;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                0)))) (show (nb078_alpha_dummy_968 h) ≠
                                        (nb078_alpha_dummy_975 h) from (by
                                        unfold nb078_alpha_dummy_975;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_974) from
                                        (by
                                          unfold nb078_alpha_dummy_974;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1014)
                                                  1)))) (show (nb078_alpha_dummy_968 h) ≠
        (nb078_alpha_dummy_976 h) from (by
                                          unfold nb078_alpha_dummy_976;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1015 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_966) ≠
        (nb078_alpha_dummy_999) from (by
          unfold nb078_alpha_dummy_999;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1044) 0)))) (show (nb078_alpha_dummy_968 h) ≠
        (nb078_alpha_dummy_1000 h) from (by
          unfold nb078_alpha_dummy_1000;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1045 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_997) from (by
          unfold nb078_alpha_dummy_997;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1042) 0)))) (show (nb078_alpha_dummy_968 h) ≠
        (nb078_alpha_dummy_998 h) from (by
          unfold nb078_alpha_dummy_998;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1043 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_966))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_968 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_980) from (by
          unfold nb078_alpha_dummy_980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_983 h) from (by
          unfold nb078_alpha_dummy_983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_979)
        from (by
          unfold nb078_alpha_dummy_979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_982 h) from (by
          unfold nb078_alpha_dummy_982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977)
        from (by
          unfold
            nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_978 h) from (by
          unfold
            nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)), ((nb078_alpha_dummy_997),
        (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)),
        ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_995),
        (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)), ((nb078_alpha_dummy_997),
        (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)),
        ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_995),
        (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠
        (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977)
        from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)),
        ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974),
        (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)),
        ((nb078_alpha_dummy_997), (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)),
        ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974),
        (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)),
        ((nb078_alpha_dummy_997), (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_997), (nb078_alpha_dummy_998 h)),
                    ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)),
                    ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
                    ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)),
                    ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)),
                    ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
                    ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
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

@[expose]
noncomputable def nb078_split_alpha_0124 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_969)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_969)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_965)
                (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_970 h)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_970 h)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_967 h)
                (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_966) from (by
                              unfold nb078_alpha_dummy_966;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1008) 1))))
                          (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_968 h) from (by
                              unfold nb078_alpha_dummy_968;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_965) from (by
                                unfold nb078_alpha_dummy_965;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1008) 0))))
                            (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_967 h) from (by
                                unfold nb078_alpha_dummy_967;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_971) from (by
                                  unfold nb078_alpha_dummy_971;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1012) 0))))
                              (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_972 h) from
                                (by
                                  unfold nb078_alpha_dummy_972;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1013 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_969) from (by
                                    unfold nb078_alpha_dummy_969;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1009) 0)))) (show
                                  (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_970 h) from (by
                                    unfold nb078_alpha_dummy_970;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1011 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_962))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_961))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_963 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_973) from
                                    (by
                                      unfold nb078_alpha_dummy_973;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1014)
                                              0)))) (show
                                    (nb078_alpha_dummy_968 h) ≠ (nb078_alpha_dummy_975 h) from
                                    (by
                                      unfold nb078_alpha_dummy_975;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1015 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_974) from (by
                                        unfold nb078_alpha_dummy_974;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                1)))) (show (nb078_alpha_dummy_968 h) ≠
                                        (nb078_alpha_dummy_976 h) from (by
                                        unfold nb078_alpha_dummy_976;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_966))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_968 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_980) from (by
          unfold nb078_alpha_dummy_980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_983 h) from (by
          unfold nb078_alpha_dummy_983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_979)
        from (by
          unfold nb078_alpha_dummy_979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_982 h) from (by
          unfold nb078_alpha_dummy_982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977)
        from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965),
        (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)),
        ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962),
        (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965),
        (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)),
        ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962),
        (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠
        (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977),
        (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)),
        ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠
        (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977),
        (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)),
        ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_966) from (by
                              unfold nb078_alpha_dummy_966;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1008) 1))))
                          (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_968 h) from (by
                              unfold nb078_alpha_dummy_968;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_965) from (by
                                unfold nb078_alpha_dummy_965;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1008) 0))))
                            (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_967 h) from (by
                                unfold nb078_alpha_dummy_967;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_971) from (by
                                  unfold nb078_alpha_dummy_971;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1012) 0))))
                              (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_972 h) from
                                (by
                                  unfold nb078_alpha_dummy_972;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1013 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_969) from (by
                                    unfold nb078_alpha_dummy_969;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1009) 0)))) (show
                                  (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_970 h) from (by
                                    unfold nb078_alpha_dummy_970;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1011 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_962))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_961))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_963 h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_973) from
                                    (by
                                      unfold nb078_alpha_dummy_973;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1014)
                                              0)))) (show
                                    (nb078_alpha_dummy_968 h) ≠ (nb078_alpha_dummy_975 h) from
                                    (by
                                      unfold nb078_alpha_dummy_975;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1015 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_966) ≠ (nb078_alpha_dummy_974) from (by
                                        unfold nb078_alpha_dummy_974;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1014)
                                                1)))) (show (nb078_alpha_dummy_968 h) ≠
                                        (nb078_alpha_dummy_976 h) from (by
                                        unfold nb078_alpha_dummy_976;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1015 h)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_966))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_968 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_980) from (by
          unfold nb078_alpha_dummy_980;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  1)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_983 h) from (by
          unfold nb078_alpha_dummy_983;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_979)
        from (by
          unfold nb078_alpha_dummy_979;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1018)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_982 h) from (by
          unfold nb078_alpha_dummy_982;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1019
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977)
        from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016)
                  0)))) (show (nb078_alpha_dummy_975 h) ≠ (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965),
        (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)),
        ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962),
        (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1022)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1023
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1020)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1021
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_987) from (by
          unfold
            nb078_alpha_dummy_987;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1026)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_988 h) from (by
          unfold
            nb078_alpha_dummy_988;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1027
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_985)
        from (by
          unfold
            nb078_alpha_dummy_985;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1024)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_986 h) from (by
          unfold
            nb078_alpha_dummy_986;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1025
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980),
        (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)),
        ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973),
        (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)),
        ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965),
        (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)),
        ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962),
        (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_973))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠
        (nb078_alpha_dummy_991) from (by
          unfold
            nb078_alpha_dummy_991;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1030)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_992 h) from (by
          unfold
            nb078_alpha_dummy_992;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1031
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_980) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1028)
                  0)))) (show (nb078_alpha_dummy_983 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1029
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠
        (nb078_alpha_dummy_993) from (by
          unfold
            nb078_alpha_dummy_993;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1034)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_994 h) from (by
          unfold
            nb078_alpha_dummy_994;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1035
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_981) ≠ (nb078_alpha_dummy_989)
        from (by
          unfold
            nb078_alpha_dummy_989;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1032)
                  0)))) (show (nb078_alpha_dummy_984 h) ≠ (nb078_alpha_dummy_990 h) from (by
          unfold
            nb078_alpha_dummy_990;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1033
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977),
        (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)),
        ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_973) ≠
        (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_973) ≠ (nb078_alpha_dummy_977) from (by
          unfold nb078_alpha_dummy_977;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1016) 0)))) (show (nb078_alpha_dummy_975 h) ≠
        (nb078_alpha_dummy_978 h) from (by
          unfold nb078_alpha_dummy_978;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1017 h) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_977),
        (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)),
        ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966),
        (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)),
        ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969),
        (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0123 x y h)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0123 x y h)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
