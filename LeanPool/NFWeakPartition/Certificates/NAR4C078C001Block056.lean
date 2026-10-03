/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block055

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part165`. -/


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
noncomputable def nb078_split_alpha_0145 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
        ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_923))
          (syn_cphi (Class.cv (nb078_alpha_dummy_890)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_923))
            (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_924 h))
          (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_924 h))
            (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_897) from
                    (by
                      unfold nb078_alpha_dummy_897;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                  (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_899 h) from (by
                      unfold nb078_alpha_dummy_899;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_898) from
                      (by
                        unfold nb078_alpha_dummy_898;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                    (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_900 h) from (by
                        unfold nb078_alpha_dummy_900;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0927 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_923) from (by
                          unfold nb078_alpha_dummy_923;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                      (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_924 h) from (by
                          unfold nb078_alpha_dummy_924;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0957 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_921) from (by
                            unfold nb078_alpha_dummy_921;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0954) 0))))
                        (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_922 h) from (by
                            unfold nb078_alpha_dummy_922;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0955 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_904) from (by
                                        unfold nb078_alpha_dummy_904;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0930)
                                                1)))) (show (nb078_alpha_dummy_899 h) ≠
                                        (nb078_alpha_dummy_907 h) from (by
                                        unfold nb078_alpha_dummy_907;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0931 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_903) from
                                        (by
                                          unfold nb078_alpha_dummy_903;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0930)
                                                  0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_906 h) from (by
                                          unfold nb078_alpha_dummy_906;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0931 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_897) ≠
        (nb078_alpha_dummy_901) from (by
          unfold nb078_alpha_dummy_901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928) 0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_902 h) from (by
          unfold nb078_alpha_dummy_902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_905),
        (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)),
                                        ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
                                        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                        ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                        ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                        ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                                        ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                                        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                                        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                                        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                                        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                                        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                        ((nb078_alpha_dummy_002), h),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠
        (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)),
        ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903),
        (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
        ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898),
        (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
        ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠
        (nb078_alpha_dummy_915) from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_915)
        from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠
        (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                unfold nb078_alpha_dummy_901;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                            (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from (by
                                unfold nb078_alpha_dummy_902;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                            ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                            ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                            ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                            ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                            ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                            ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                            ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                            ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                            ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                            ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                            ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                            ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                            ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                            ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                              unfold nb078_alpha_dummy_901;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                          (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from (by
                              unfold nb078_alpha_dummy_902;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                unfold nb078_alpha_dummy_901;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                            (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from (by
                                unfold nb078_alpha_dummy_902;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                            ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                            ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                            ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                            ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                            ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                            ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                            ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                            ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                            ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                            ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                            ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                            ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                            ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                            ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                            ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_897) from (by
                        unfold nb078_alpha_dummy_897;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                    (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_899 h) from (by
                        unfold nb078_alpha_dummy_899;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0927 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_898) from (by
                          unfold nb078_alpha_dummy_898;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                      (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_900 h) from (by
                          unfold nb078_alpha_dummy_900;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_923) from (by
                            unfold nb078_alpha_dummy_923;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                        (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_924 h) from (by
                            unfold nb078_alpha_dummy_924;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0957 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_921) from (by
                              unfold nb078_alpha_dummy_921;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0954) 0))))
                          (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_922 h) from (by
                              unfold nb078_alpha_dummy_922;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0955 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_904) from
                                        (by
                                          unfold nb078_alpha_dummy_904;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0930)
                                                  1)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_907 h) from (by
                                          unfold nb078_alpha_dummy_907;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0931 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_897) ≠
        (nb078_alpha_dummy_903) from (by
          unfold nb078_alpha_dummy_903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_906 h) from (by
          unfold nb078_alpha_dummy_906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
          unfold nb078_alpha_dummy_901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928) 0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_902 h) from (by
          unfold nb078_alpha_dummy_902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_905),
        (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)),
        ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901),
        (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
        ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923),
        (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130),
        (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠
        (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_911) from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_911)
        from (by
          unfold
            nb078_alpha_dummy_911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_912 h) from (by
          unfold
            nb078_alpha_dummy_912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_909)
        from (by
          unfold
            nb078_alpha_dummy_909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_910 h) from (by
          unfold
            nb078_alpha_dummy_910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904),
        (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897),
        (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
        ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921),
        (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919),
        (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847),
        (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠
        (nb078_alpha_dummy_915) from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_915)
        from (by
          unfold
            nb078_alpha_dummy_915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_916 h) from (by
          unfold
            nb078_alpha_dummy_916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078_alpha_dummy_907 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠
        (nb078_alpha_dummy_917) from (by
          unfold
            nb078_alpha_dummy_917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_918 h) from (by
          unfold
            nb078_alpha_dummy_918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_905) ≠ (nb078_alpha_dummy_913)
        from (by
          unfold
            nb078_alpha_dummy_913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078_alpha_dummy_908 h) ≠ (nb078_alpha_dummy_914 h) from (by
          unfold
            nb078_alpha_dummy_914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                  unfold nb078_alpha_dummy_901;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                              (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from
                                (by
                                  unfold nb078_alpha_dummy_902;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                              ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                              ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                              ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                              ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                              ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                              ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                              ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                              ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                              ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                              ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                              ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                              ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                              ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                              ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                              ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                unfold nb078_alpha_dummy_901;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                            (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from (by
                                unfold nb078_alpha_dummy_902;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                  unfold nb078_alpha_dummy_901;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                              (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from
                                (by
                                  unfold nb078_alpha_dummy_902;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                              ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                              ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                              ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                              ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                              ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                              ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                              ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                              ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                              ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                              ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                              ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                              ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
                              ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
                              ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                              ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb078_split_alpha_0146 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)),
        ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_1133))
          (syn_cop (Class.cv (nb078_alpha_dummy_1129)) (Class.cv (nb078_alpha_dummy_1130))))
        (Wff.neg (syn_wbr (Class.cv (nb078_alpha_dummy_1130))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1129)))))
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_1134 h))
          (syn_cop (Class.cv (nb078_alpha_dummy_1131 h)) (Class.cv (nb078_alpha_dummy_1132 h))))
        (Wff.neg (syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb078_alpha_dummy_1131 h))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1133) from (by
                unfold nb078_alpha_dummy_1133;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1178) 0))))) (Ne.symm
            (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1134 h) from (by
                unfold nb078_alpha_dummy_1134;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1179 h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1133) from (by
                  unfold nb078_alpha_dummy_1133;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1176) 0)))))
            (Ne.symm (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1134 h) from (by
                  unfold nb078_alpha_dummy_1134;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1177 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0138 x y h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1136) from (by
                                      unfold nb078_alpha_dummy_1136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1208)
                                              1)))) (show (nb078_alpha_dummy_1132 h) ≠
                                      (nb078_alpha_dummy_1138 h) from (by
                                      unfold nb078_alpha_dummy_1138;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1210 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1135) from
                                      (by
                                        unfold nb078_alpha_dummy_1135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1208)
                                                0)))) (show (nb078_alpha_dummy_1132 h) ≠
                                        (nb078_alpha_dummy_1137 h) from (by
                                        unfold nb078_alpha_dummy_1137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1210 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1165) from
                                        (by
                                          unfold nb078_alpha_dummy_1165;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1212)
                                                  0)))) (show (nb078_alpha_dummy_1132 h) ≠
        (nb078_alpha_dummy_1166 h) from (by
                                          unfold nb078_alpha_dummy_1166;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1213 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1130) ≠
        (nb078_alpha_dummy_1139) from (by
          unfold nb078_alpha_dummy_1139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1209) 0)))) (show (nb078_alpha_dummy_1132 h) ≠
        (nb078_alpha_dummy_1140 h) from (by
          unfold nb078_alpha_dummy_1140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1211 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_1129))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_1130))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_1132 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0139 x y h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1167),
        (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
        ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165),
        (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c])))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1136) from (by
                                      unfold nb078_alpha_dummy_1136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1208)
                                              1)))) (show (nb078_alpha_dummy_1132 h) ≠
                                      (nb078_alpha_dummy_1138 h) from (by
                                      unfold nb078_alpha_dummy_1138;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1210 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1135) from
                                      (by
                                        unfold nb078_alpha_dummy_1135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1208)
                                                0)))) (show (nb078_alpha_dummy_1132 h) ≠
                                        (nb078_alpha_dummy_1137 h) from (by
                                        unfold nb078_alpha_dummy_1137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1210 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1165) from
                                        (by
                                          unfold nb078_alpha_dummy_1165;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1212)
                                                  0)))) (show (nb078_alpha_dummy_1132 h) ≠
        (nb078_alpha_dummy_1166 h) from (by
                                          unfold nb078_alpha_dummy_1166;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1213 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1130) ≠
        (nb078_alpha_dummy_1139) from (by
          unfold nb078_alpha_dummy_1139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1209) 0)))) (show (nb078_alpha_dummy_1132 h) ≠
        (nb078_alpha_dummy_1140 h) from (by
          unfold nb078_alpha_dummy_1140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1211 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_1129))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_1130))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_1132 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0139 x y h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1167),
        (nb078_alpha_dummy_1168 h)), ((nb078_alpha_dummy_1136), (nb078_alpha_dummy_1138 h)),
        ((nb078_alpha_dummy_1135), (nb078_alpha_dummy_1137 h)), ((nb078_alpha_dummy_1165),
        (nb078_alpha_dummy_1166 h)), ((nb078_alpha_dummy_1139), (nb078_alpha_dummy_1140 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
                                          simp only [fv_syn_ccompl, fv_syn_csn,
                                            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0140 x y h)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1172) from
                                      (by
                                        unfold nb078_alpha_dummy_1172;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1246)
                                                1)))) (show (nb078_alpha_dummy_1131 h) ≠
                                        (nb078_alpha_dummy_1174 h) from (by
                                        unfold nb078_alpha_dummy_1174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1248 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1171) from
                                        (by
                                          unfold nb078_alpha_dummy_1171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1246)
                                                  0)))) (show (nb078_alpha_dummy_1131 h) ≠
        (nb078_alpha_dummy_1173 h) from (by
                                          unfold nb078_alpha_dummy_1173;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1248 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1129) ≠
        (nb078_alpha_dummy_1201) from (by
          unfold nb078_alpha_dummy_1201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1250) 0)))) (show (nb078_alpha_dummy_1131 h) ≠
        (nb078_alpha_dummy_1202 h) from (by
          unfold nb078_alpha_dummy_1202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1251 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1175) from (by
          unfold nb078_alpha_dummy_1175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1247) 0)))) (show (nb078_alpha_dummy_1131 h) ≠
        (nb078_alpha_dummy_1176 h) from (by
          unfold nb078_alpha_dummy_1176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1249 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪
                                        ((Class.cv (nb078_alpha_dummy_1129))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
                                        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0141 x y h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1203),
        (nb078_alpha_dummy_1204 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
        ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1201),
        (nb078_alpha_dummy_1202 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1172) from
                                      (by
                                        unfold nb078_alpha_dummy_1172;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1246)
                                                1)))) (show (nb078_alpha_dummy_1131 h) ≠
                                        (nb078_alpha_dummy_1174 h) from (by
                                        unfold nb078_alpha_dummy_1174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1248 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1171) from
                                        (by
                                          unfold nb078_alpha_dummy_1171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1246)
                                                  0)))) (show (nb078_alpha_dummy_1131 h) ≠
        (nb078_alpha_dummy_1173 h) from (by
                                          unfold nb078_alpha_dummy_1173;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1248 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_1129) ≠
        (nb078_alpha_dummy_1201) from (by
          unfold nb078_alpha_dummy_1201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1250) 0)))) (show (nb078_alpha_dummy_1131 h) ≠
        (nb078_alpha_dummy_1202 h) from (by
          unfold nb078_alpha_dummy_1202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1251 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1175) from (by
          unfold nb078_alpha_dummy_1175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1247) 0)))) (show (nb078_alpha_dummy_1131 h) ≠
        (nb078_alpha_dummy_1176 h) from (by
          unfold nb078_alpha_dummy_1176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1249 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪
                                        ((Class.cv (nb078_alpha_dummy_1129))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
                                        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0141 x y h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_1203),
        (nb078_alpha_dummy_1204 h)), ((nb078_alpha_dummy_1172), (nb078_alpha_dummy_1174 h)),
        ((nb078_alpha_dummy_1171), (nb078_alpha_dummy_1173 h)), ((nb078_alpha_dummy_1201),
        (nb078_alpha_dummy_1202 h)), ((nb078_alpha_dummy_1175), (nb078_alpha_dummy_1176 h)),
        ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)), ((nb078_alpha_dummy_1129),
        (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133), (nb078_alpha_dummy_1134 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047),
        (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
                                    (mem_lt_freshVar (nb078_support_mem_0878) 0))))) (Ne.symm
                          (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_852 h) from (by
                              unfold nb078_alpha_dummy_852;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0879 h) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb078_split_alpha_0142 x y h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_854) from (by
          unfold nb078_alpha_dummy_854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910) 1)))) (show (nb078_alpha_dummy_850 h) ≠
        (nb078_alpha_dummy_856 h) from (by
          unfold nb078_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853) from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910) 0)))) (show (nb078_alpha_dummy_850 h) ≠
        (nb078_alpha_dummy_855 h) from (by
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
                  (nb078_support_mem_0915 h)
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
                  (nb078_support_mem_0913 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_847))).fv ∪
        ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0143 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_854) from (by
          unfold nb078_alpha_dummy_854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910) 1)))) (show (nb078_alpha_dummy_850 h) ≠
        (nb078_alpha_dummy_856 h) from (by
          unfold nb078_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853) from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910) 0)))) (show (nb078_alpha_dummy_850 h) ≠
        (nb078_alpha_dummy_855 h) from (by
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
                  (nb078_support_mem_0915 h)
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
                  (nb078_support_mem_0913 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_847))).fv ∪
        ((Class.cv (nb078_alpha_dummy_848))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0143 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb078_split_alpha_0144 x y h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_890) from (by
          unfold nb078_alpha_dummy_890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948) 1)))) (show (nb078_alpha_dummy_849 h) ≠
        (nb078_alpha_dummy_892 h) from (by
          unfold nb078_alpha_dummy_892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889) from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948) 0)))) (show (nb078_alpha_dummy_849 h) ≠
        (nb078_alpha_dummy_891 h) from (by
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
                  (nb078_support_mem_0953 h)
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
                  (nb078_support_mem_0951 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv) (by decide)) (freshVar_injective
        (((Class.cv h)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_849 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0145 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_890) from (by
          unfold nb078_alpha_dummy_890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948) 1)))) (show (nb078_alpha_dummy_849 h) ≠
        (nb078_alpha_dummy_892 h) from (by
          unfold nb078_alpha_dummy_892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889) from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948) 0)))) (show (nb078_alpha_dummy_849 h) ≠
        (nb078_alpha_dummy_891 h) from (by
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
                  (nb078_support_mem_0953 h)
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
                  (nb078_support_mem_0951 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv) (by decide)) (freshVar_injective
        (((Class.cv h)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_849 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0145 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1130), (nb078_alpha_dummy_1132 h)),
        ((nb078_alpha_dummy_1129), (nb078_alpha_dummy_1131 h)), ((nb078_alpha_dummy_1133),
        (nb078_alpha_dummy_1134 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045),
        (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
                            (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1130) from (by
                                unfold nb078_alpha_dummy_1130;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1266) 1))))
                            (show h ≠ (nb078_alpha_dummy_1132 h) from (by
                                unfold nb078_alpha_dummy_1132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1267 h) 1))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1129) from (by
                                  unfold nb078_alpha_dummy_1129;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1266) 0))))
                              (show h ≠ (nb078_alpha_dummy_1131 h) from (by
                                  unfold nb078_alpha_dummy_1131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1267 h) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1133) from
                                  (by
                                    unfold nb078_alpha_dummy_1133;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1264) 0))))
                                (show h ≠ (nb078_alpha_dummy_1134 h) from (by
                                    unfold nb078_alpha_dummy_1134;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1265 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1051) from
                                    (by
                                      unfold nb078_alpha_dummy_1051;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1260)
                                              2)))) (show h ≠ (nb078_alpha_dummy_1054 h) from
                                    (by
                                      unfold nb078_alpha_dummy_1054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1262 h)
                                              2)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1050) from
                                      (by
                                        unfold nb078_alpha_dummy_1050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1260)
                                                1)))) (show h ≠ (nb078_alpha_dummy_1053 h) from
                                      (by
                                        unfold nb078_alpha_dummy_1053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1262 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1049) from
                                        (by
                                          unfold nb078_alpha_dummy_1049;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1260)
                                                  0))))
                                      (show h ≠ (nb078_alpha_dummy_1052 h) from (by
                                          unfold nb078_alpha_dummy_1052;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1262 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠
        (nb078_alpha_dummy_1055) from (by
          unfold nb078_alpha_dummy_1055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1261) 0)))) (show h ≠ (nb078_alpha_dummy_1056 h) from (by
          unfold nb078_alpha_dummy_1056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1263 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1047) from (by
          unfold nb078_alpha_dummy_1047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1258) 0)))) (show h ≠ (nb078_alpha_dummy_1048 h) from (by
          unfold nb078_alpha_dummy_1048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1259 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1045) from (by
          unfold nb078_alpha_dummy_1045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1256) 0)))) (show h ≠ (nb078_alpha_dummy_1046 h) from (by
          unfold nb078_alpha_dummy_1046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1257 h) 0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part166`. -/


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
noncomputable def nb078_split_alpha_0147 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
        ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1213))
          (Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1213)) (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1214 h))
          (Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1214 h))
            (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1208) from
                    (by
                      unfold nb078_alpha_dummy_1208;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
                  (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1210 h) from (by
                      unfold nb078_alpha_dummy_1210;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1207) from (by
                        unfold nb078_alpha_dummy_1207;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0))))
                    (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1209 h) from (by
                        unfold nb078_alpha_dummy_1209;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1270 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1213) from (by
                          unfold nb078_alpha_dummy_1213;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1272) 0))))
                      (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1214 h) from (by
                          unfold nb078_alpha_dummy_1214;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1273 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1211) from (by
                            unfold nb078_alpha_dummy_1211;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1269) 0))))
                        (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1212 h) from (by
                            unfold nb078_alpha_dummy_1212;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1271 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1051))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1215) from (by
                              unfold nb078_alpha_dummy_1215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                          (show (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1217 h) from (by
                              unfold nb078_alpha_dummy_1217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1216) from (by
                                unfold nb078_alpha_dummy_1216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 1))))
                            (show (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1218 h) from
                              (by
                                unfold nb078_alpha_dummy_1218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1222) from (by
          unfold nb078_alpha_dummy_1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1225 h) from (by
          unfold nb078_alpha_dummy_1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1221) from (by
          unfold nb078_alpha_dummy_1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1224 h) from (by
          unfold nb078_alpha_dummy_1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from (by
          unfold nb078_alpha_dummy_1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276) 0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1220 h) from (by
          unfold nb078_alpha_dummy_1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207),
        (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
        ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207),
        (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
        ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                      (by
                                        unfold nb078_alpha_dummy_1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                        (nb078_alpha_dummy_1220 h) from (by
                                        unfold nb078_alpha_dummy_1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                    ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                    ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                    ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                    ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                    ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
                                    ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from (by
                                      unfold nb078_alpha_dummy_1219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1276)
                                              0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                      (nb078_alpha_dummy_1220 h) from (by
                                      unfold nb078_alpha_dummy_1220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1277 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                      (by
                                        unfold nb078_alpha_dummy_1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                        (nb078_alpha_dummy_1220 h) from (by
                                        unfold nb078_alpha_dummy_1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                    ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                    ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                    ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                    ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                    ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
                                    ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                    ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1208) from (by
                        unfold nb078_alpha_dummy_1208;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
                    (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1210 h) from (by
                        unfold nb078_alpha_dummy_1210;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1270 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1207) from (by
                          unfold nb078_alpha_dummy_1207;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1268) 0))))
                      (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1209 h) from (by
                          unfold nb078_alpha_dummy_1209;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1270 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1213) from (by
                            unfold nb078_alpha_dummy_1213;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1272) 0))))
                        (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1214 h) from (by
                            unfold nb078_alpha_dummy_1214;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1273 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1211) from (by
                              unfold nb078_alpha_dummy_1211;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1269) 0))))
                          (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1212 h) from (by
                              unfold nb078_alpha_dummy_1212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1271 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_1051))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1215) from (by
                                unfold nb078_alpha_dummy_1215;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                            (show (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1217 h) from
                              (by
                                unfold nb078_alpha_dummy_1217;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1208) ≠ (nb078_alpha_dummy_1216) from (by
                                  unfold nb078_alpha_dummy_1216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1274) 1)))) (show
                                (nb078_alpha_dummy_1210 h) ≠ (nb078_alpha_dummy_1218 h) from (by
                                  unfold nb078_alpha_dummy_1218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_1208))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_1210 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1222) from (by
          unfold nb078_alpha_dummy_1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1225 h) from (by
          unfold nb078_alpha_dummy_1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1221) from (by
          unfold nb078_alpha_dummy_1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1224 h) from (by
          unfold nb078_alpha_dummy_1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1215) ≠
        (nb078_alpha_dummy_1219) from (by
          unfold nb078_alpha_dummy_1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276)
                  0)))) (show (nb078_alpha_dummy_1217 h) ≠ (nb078_alpha_dummy_1220 h) from (by
          unfold nb078_alpha_dummy_1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207),
        (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
        ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1229) from (by
          unfold
            nb078_alpha_dummy_1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1230 h) from (by
          unfold
            nb078_alpha_dummy_1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1227) from (by
          unfold
            nb078_alpha_dummy_1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1228 h) from (by
          unfold
            nb078_alpha_dummy_1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1223), (nb078_alpha_dummy_1226 h)), ((nb078_alpha_dummy_1222),
        (nb078_alpha_dummy_1225 h)), ((nb078_alpha_dummy_1221), (nb078_alpha_dummy_1224 h)),
        ((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)), ((nb078_alpha_dummy_1215),
        (nb078_alpha_dummy_1217 h)), ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
        ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)), ((nb078_alpha_dummy_1207),
        (nb078_alpha_dummy_1209 h)), ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
        ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
        ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1215))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1217
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1222) ≠ (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1233) from (by
          unfold
            nb078_alpha_dummy_1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1234 h) from (by
          unfold
            nb078_alpha_dummy_1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1222) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078_alpha_dummy_1225 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1223) ≠ (nb078_alpha_dummy_1235) from (by
          unfold
            nb078_alpha_dummy_1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1236 h) from (by
          unfold
            nb078_alpha_dummy_1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1223) ≠
        (nb078_alpha_dummy_1231) from (by
          unfold
            nb078_alpha_dummy_1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078_alpha_dummy_1226 h) ≠ (nb078_alpha_dummy_1232 h) from (by
          unfold
            nb078_alpha_dummy_1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                        (by
                                          unfold nb078_alpha_dummy_1219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1276)
                                                  0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1220 h) from (by
                                          unfold nb078_alpha_dummy_1220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1277 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                      ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                      ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                      ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                      ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                      ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
                                      ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                      (by
                                        unfold nb078_alpha_dummy_1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078_alpha_dummy_1217 h) ≠
                                        (nb078_alpha_dummy_1220 h) from (by
                                        unfold nb078_alpha_dummy_1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1215) ≠ (nb078_alpha_dummy_1219) from
                                        (by
                                          unfold nb078_alpha_dummy_1219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1276)
                                                  0)))) (show (nb078_alpha_dummy_1217 h) ≠
        (nb078_alpha_dummy_1220 h) from (by
                                          unfold nb078_alpha_dummy_1220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1277 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1219), (nb078_alpha_dummy_1220 h)),
                                      ((nb078_alpha_dummy_1215), (nb078_alpha_dummy_1217 h)),
                                      ((nb078_alpha_dummy_1216), (nb078_alpha_dummy_1218 h)),
                                      ((nb078_alpha_dummy_1208), (nb078_alpha_dummy_1210 h)),
                                      ((nb078_alpha_dummy_1207), (nb078_alpha_dummy_1209 h)),
                                      ((nb078_alpha_dummy_1213), (nb078_alpha_dummy_1214 h)),
                                      ((nb078_alpha_dummy_1211), (nb078_alpha_dummy_1212 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                                      ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
