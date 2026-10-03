/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block064

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part188`. -/


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
noncomputable def nb078_split_alpha_0171 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_895))
          (Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_895)) (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_896 h))
          (Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_896 h))
            (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_890) from
                    (by
                      unfold nb078_alpha_dummy_890;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                  (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_892 h) from (by
                      unfold nb078_alpha_dummy_892;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_889) from
                      (by
                        unfold nb078_alpha_dummy_889;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                    (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_891 h) from (by
                        unfold nb078_alpha_dummy_891;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_895) from (by
                          unfold nb078_alpha_dummy_895;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_896 h) from (by
                          unfold nb078_alpha_dummy_896;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_893) from (by
                            unfold nb078_alpha_dummy_893;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_894 h) from (by
                            unfold nb078_alpha_dummy_894;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_848))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_847))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_849 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_897) from (by
                              unfold nb078_alpha_dummy_897;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                          (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_899 h) from (by
                              unfold nb078_alpha_dummy_899;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                          (TAlphaVar.there
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_904) from (by
          unfold nb078_alpha_dummy_904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_907 h) from (by
          unfold nb078_alpha_dummy_907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_903) from (by
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
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904),
        (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897),
        (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_915) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                        unfold nb078_alpha_dummy_901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078_alpha_dummy_899 h) ≠
                                        (nb078_alpha_dummy_902 h) from (by
                                        unfold nb078_alpha_dummy_902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                    ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                    ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from
                                    (by
                                      unfold nb078_alpha_dummy_901;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0928)
                                              0)))) (show
                                    (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from
                                    (by
                                      unfold nb078_alpha_dummy_902;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0929 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                        unfold nb078_alpha_dummy_901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078_alpha_dummy_899 h) ≠
                                        (nb078_alpha_dummy_902 h) from (by
                                        unfold nb078_alpha_dummy_902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                    ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                    ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                    ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                    ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                    ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_890) from
                      (by
                        unfold nb078_alpha_dummy_890;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                    (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_892 h) from (by
                        unfold nb078_alpha_dummy_892;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_889) from (by
                          unfold nb078_alpha_dummy_889;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_891 h) from (by
                          unfold nb078_alpha_dummy_891;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_895) from (by
                            unfold nb078_alpha_dummy_895;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_896 h) from (by
                            unfold nb078_alpha_dummy_896;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_893) from (by
                              unfold nb078_alpha_dummy_893;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                          (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_894 h) from (by
                              unfold nb078_alpha_dummy_894;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_848))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_847))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_849 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_897) from (by
                                unfold nb078_alpha_dummy_897;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                            (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_899 h) from (by
                                unfold nb078_alpha_dummy_899;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_898) from (by
                                  unfold nb078_alpha_dummy_898;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                              (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_900 h) from
                                (by
                                  unfold nb078_alpha_dummy_900;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_892 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_904) from (by
          unfold nb078_alpha_dummy_904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_907 h) from (by
          unfold nb078_alpha_dummy_907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_903) from (by
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
                  (nb078_support_mem_0931 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901)
        from (by
          unfold nb078_alpha_dummy_901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928)
                  0)))) (show (nb078_alpha_dummy_899 h) ≠ (nb078_alpha_dummy_902 h) from (by
          unfold nb078_alpha_dummy_902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904),
        (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)),
        ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897),
        (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889),
        (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848),
        (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_904) ≠ (nb078_alpha_dummy_915) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from
                                        (by
                                          unfold nb078_alpha_dummy_901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_902 h) from (by
                                          unfold nb078_alpha_dummy_902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                      ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                      ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                      ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                      ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                      ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                      ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from (by
                                        unfold nb078_alpha_dummy_901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078_alpha_dummy_899 h) ≠
                                        (nb078_alpha_dummy_902 h) from (by
                                        unfold nb078_alpha_dummy_902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_897) ≠ (nb078_alpha_dummy_901) from
                                        (by
                                          unfold nb078_alpha_dummy_901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078_alpha_dummy_899 h) ≠
        (nb078_alpha_dummy_902 h) from (by
                                          unfold nb078_alpha_dummy_902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)),
                                      ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)),
                                      ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)),
                                      ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                      ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                      ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
                                      ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                      ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                      ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                      ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                      ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                      ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                      ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                      ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part189`. -/


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
noncomputable def nb078_split_alpha_0172 (x : Var) (y : Var) (h : Var) :
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
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
                                        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                                        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                                        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                                        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
                            ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                            ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                            ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                            ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051),
        (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
        ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055),
        (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
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
        ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050),
        (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
        ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
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
                              ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
                              ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)),
                              ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)),
                              ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part190`. -/


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
noncomputable def nb078_split_alpha_0173 (x : Var) (y : Var) (h : Var) (dv_h_x : h ≠ x)
    (dv_h_y : h ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (syn_wf (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_003))
          (Class.cv (nb078_alpha_dummy_004)))
        (Wff.neg (syn_wfun (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))))
      (Wff.imp (syn_wf (Class.cv h) (Class.cv x) (Class.cv y))
        (Wff.neg (syn_wfun (syn_ccnv (Class.cv h))))) :=
  (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.neg (nb078_split_alpha_0129 x y h dv_h_x dv_x_y))
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0130 x y h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1010) from (by
          unfold
            nb078_alpha_dummy_1010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  1)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1012 h) from (by
          unfold
            nb078_alpha_dummy_1012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1009) from (by
          unfold
            nb078_alpha_dummy_1009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold
            nb078_alpha_dummy_1011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1039) from (by
          unfold
            nb078_alpha_dummy_1039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1080)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1040 h) from (by
          unfold
            nb078_alpha_dummy_1040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1081
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1013) from (by
          unfold
            nb078_alpha_dummy_1013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1077)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1014 h) from (by
          unfold
            nb078_alpha_dummy_1014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1079
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_1007 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0131 x y h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1010) from (by
          unfold
            nb078_alpha_dummy_1010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  1)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1012 h) from (by
          unfold
            nb078_alpha_dummy_1012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1009) from (by
          unfold
            nb078_alpha_dummy_1009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold
            nb078_alpha_dummy_1011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1039) from (by
          unfold
            nb078_alpha_dummy_1039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1080)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1040 h) from (by
          unfold
            nb078_alpha_dummy_1040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1081
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1013) from (by
          unfold
            nb078_alpha_dummy_1013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1077)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1014 h) from (by
          unfold
            nb078_alpha_dummy_1014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1079
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_1007 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0131 x y h))))))))))))))))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1006) from
                                      (by
                                        unfold nb078_alpha_dummy_1006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1090)
                                                1)))) (show h ≠ (nb078_alpha_dummy_1008 h) from
                                      (by
                                        unfold nb078_alpha_dummy_1008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1091 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1005) from
                                        (by
                                          unfold nb078_alpha_dummy_1005;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1090)
                                                  0))))
                                      (show h ≠ (nb078_alpha_dummy_1007 h) from (by
                                          unfold nb078_alpha_dummy_1007;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1091 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠
        (nb078_alpha_dummy_1003) from (by
          unfold nb078_alpha_dummy_1003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1088) 0)))) (show h ≠ (nb078_alpha_dummy_1004 y h) from (by
          unfold nb078_alpha_dummy_1004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1089 y h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1001) from (by
          unfold nb078_alpha_dummy_1001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1086) 0)))) (show h ≠ (nb078_alpha_dummy_1002 y h) from (by
          unfold nb078_alpha_dummy_1002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1087 y h) 0)))) (TAlphaVar.here _ _ _)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_004) ≠ (nb078_alpha_dummy_1003) from (by
                                unfold nb078_alpha_dummy_1003;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1094) 0))))
                            (show y ≠ (nb078_alpha_dummy_1004 y h) from (by
                                unfold nb078_alpha_dummy_1004;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1095 y h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_004) ≠ (nb078_alpha_dummy_1001) from (by
                                  unfold nb078_alpha_dummy_1001;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1092) 0))))
                              (show y ≠ (nb078_alpha_dummy_1002 y h) from (by
                                  unfold nb078_alpha_dummy_1002;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1093 y h)
                                          0)))) (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_h_y) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0130 x y h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1010) from (by
          unfold
            nb078_alpha_dummy_1010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  1)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1012 h) from (by
          unfold
            nb078_alpha_dummy_1012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1009) from (by
          unfold
            nb078_alpha_dummy_1009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold
            nb078_alpha_dummy_1011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1039) from (by
          unfold
            nb078_alpha_dummy_1039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1080)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1040 h) from (by
          unfold
            nb078_alpha_dummy_1040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1081
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1013) from (by
          unfold
            nb078_alpha_dummy_1013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1077)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1014 h) from (by
          unfold
            nb078_alpha_dummy_1014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1079
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_1007 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0131 x y h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1010) from (by
          unfold
            nb078_alpha_dummy_1010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  1)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1012 h) from (by
          unfold
            nb078_alpha_dummy_1012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1009) from (by
          unfold
            nb078_alpha_dummy_1009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1076)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold
            nb078_alpha_dummy_1011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1078
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1039) from (by
          unfold
            nb078_alpha_dummy_1039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1080)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1040 h) from (by
          unfold
            nb078_alpha_dummy_1040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1081
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1005) ≠
        (nb078_alpha_dummy_1013) from (by
          unfold
            nb078_alpha_dummy_1013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1077)
                  0)))) (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1014 h) from (by
          unfold
            nb078_alpha_dummy_1014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1079
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv h)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_1007 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0131 x y h))))))))))))))))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1006) from
                                      (by
                                        unfold nb078_alpha_dummy_1006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1090)
                                                1)))) (show h ≠ (nb078_alpha_dummy_1008 h) from
                                      (by
                                        unfold nb078_alpha_dummy_1008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1091 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1005) from
                                        (by
                                          unfold nb078_alpha_dummy_1005;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1090)
                                                  0))))
                                      (show h ≠ (nb078_alpha_dummy_1007 h) from (by
                                          unfold nb078_alpha_dummy_1007;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1091 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠
        (nb078_alpha_dummy_1003) from (by
          unfold nb078_alpha_dummy_1003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1088) 0)))) (show h ≠ (nb078_alpha_dummy_1004 y h) from (by
          unfold nb078_alpha_dummy_1004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1089 y h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1001) from (by
          unfold nb078_alpha_dummy_1001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1086) 0)))) (show h ≠ (nb078_alpha_dummy_1002 y h) from (by
          unfold nb078_alpha_dummy_1002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1087 y h) 0)))) (TAlphaVar.here _ _ _)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_004) ≠ (nb078_alpha_dummy_1003) from (by
                                unfold nb078_alpha_dummy_1003;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1094) 0))))
                            (show y ≠ (nb078_alpha_dummy_1004 y h) from (by
                                unfold nb078_alpha_dummy_1004;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1095 y h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_004) ≠ (nb078_alpha_dummy_1001) from (by
                                  unfold nb078_alpha_dummy_1001;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1092) 0))))
                              (show y ≠ (nb078_alpha_dummy_1002 y h) from (by
                                  unfold nb078_alpha_dummy_1002;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1093 y h)
                                          0)))) (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_h_y) (TAlphaVar.here _ _ _)))))))))))))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_cvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0133 x y h))))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1006) from (by
                        unfold nb078_alpha_dummy_1006;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1090) 1))))
                    (show h ≠ (nb078_alpha_dummy_1008 h) from (by
                        unfold nb078_alpha_dummy_1008;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1091 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1005) from (by
                          unfold nb078_alpha_dummy_1005;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1090) 0))))
                      (show h ≠ (nb078_alpha_dummy_1007 h) from (by
                          unfold nb078_alpha_dummy_1007;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1091 h) 0))))
                      (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb078_split_alpha_0153 x y h))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn
                          [((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cid) (nb078_wpp_refl_0509 x y h)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb078_split_alpha_0153 x y h))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn
                          [((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)),
                            ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)),
                            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cid) (nb078_wpp_refl_0509 x y h)))))))))) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (Ne.symm
                        (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1055) from (by
                            unfold nb078_alpha_dummy_1055;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1098) 0))))) (Ne.symm
                        (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1056 h) from (by
                            unfold nb078_alpha_dummy_1056;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1099 h) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1055) from (by
                              unfold nb078_alpha_dummy_1055;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1096) 0))))) (Ne.symm
                          (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1056 h) from (by
                              unfold nb078_alpha_dummy_1056;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1097 h) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb078_split_alpha_0154 x y h)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1058) from (by
          unfold nb078_alpha_dummy_1058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1128) 1)))) (show (nb078_alpha_dummy_1053 h) ≠
        (nb078_alpha_dummy_1060 h) from (by
          unfold nb078_alpha_dummy_1060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1130 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1057) from (by
          unfold nb078_alpha_dummy_1057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1128) 0)))) (show (nb078_alpha_dummy_1053 h) ≠
        (nb078_alpha_dummy_1059 h) from (by
          unfold nb078_alpha_dummy_1059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1130 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1087) from (by
          unfold nb078_alpha_dummy_1087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1132)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1088 h) from (by
          unfold nb078_alpha_dummy_1088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1133 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1061) from (by
          unfold nb078_alpha_dummy_1061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1129)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1062 h) from (by
          unfold nb078_alpha_dummy_1062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1131 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb078_split_alpha_0155 x y h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1058) from (by
          unfold nb078_alpha_dummy_1058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1128) 1)))) (show (nb078_alpha_dummy_1053 h) ≠
        (nb078_alpha_dummy_1060 h) from (by
          unfold nb078_alpha_dummy_1060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1130 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1057) from (by
          unfold nb078_alpha_dummy_1057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1128) 0)))) (show (nb078_alpha_dummy_1053 h) ≠
        (nb078_alpha_dummy_1059 h) from (by
          unfold nb078_alpha_dummy_1059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1130 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1087) from (by
          unfold nb078_alpha_dummy_1087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1132)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1088 h) from (by
          unfold nb078_alpha_dummy_1088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1133 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1061) from (by
          unfold nb078_alpha_dummy_1061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1129)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1062 h) from (by
          unfold nb078_alpha_dummy_1062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1131 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb078_split_alpha_0155 x y h)))))))))))))
                (TAlphaWff.ex (TAlphaWff.conj (nb078_split_alpha_0166 x y h) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0167 x y h)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1208) from (by
          unfold nb078_alpha_dummy_1208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296)
                  1)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1210 h) from (by
          unfold nb078_alpha_dummy_1210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1207) from (by
          unfold nb078_alpha_dummy_1207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1209 h) from (by
          unfold nb078_alpha_dummy_1209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1237) from (by
          unfold nb078_alpha_dummy_1237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1300)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1238 h) from (by
          unfold nb078_alpha_dummy_1238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1301
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1211) from (by
          unfold nb078_alpha_dummy_1211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1297)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1212 h) from (by
          unfold nb078_alpha_dummy_1212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1299
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb078_alpha_dummy_002))))).fv) (by decide)) (freshVar_injective (((syn_ccnv
        (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0168 x y h))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1208) from (by
          unfold nb078_alpha_dummy_1208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296)
                  1)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1210 h) from (by
          unfold nb078_alpha_dummy_1210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1207) from (by
          unfold nb078_alpha_dummy_1207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1209 h) from (by
          unfold nb078_alpha_dummy_1209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1237) from (by
          unfold nb078_alpha_dummy_1237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1300)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1238 h) from (by
          unfold nb078_alpha_dummy_1238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1301
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1050) ≠
        (nb078_alpha_dummy_1211) from (by
          unfold nb078_alpha_dummy_1211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1297)
                  0)))) (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1212 h) from (by
          unfold nb078_alpha_dummy_1212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1299
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb078_alpha_dummy_002))))).fv) (by decide)) (freshVar_injective (((syn_ccnv
        (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1054 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0168 x y h)))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (Ne.symm (show
                                        (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_851) from
                                        (by
                                          unfold nb078_alpha_dummy_851;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0880)
                                                  0))))) (Ne.symm (show
                                        (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_852 h)
                                        from (by
                                          unfold nb078_alpha_dummy_852;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0881 h) 0)))))
                                    (TAlphaVar.there (Ne.symm (show (nb078_alpha_dummy_847) ≠
        (nb078_alpha_dummy_851) from (by
          unfold nb078_alpha_dummy_851;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0878) 0))))) (Ne.symm (show (nb078_alpha_dummy_849 h) ≠
        (nb078_alpha_dummy_852 h) from (by
          unfold nb078_alpha_dummy_852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0879 h) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0169 x y h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_854) from (by
          unfold
            nb078_alpha_dummy_854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_856 h) from (by
          unfold
            nb078_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853)
        from (by
          unfold
            nb078_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold
            nb078_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_883)
        from (by
          unfold
            nb078_alpha_dummy_883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_884 h) from (by
          unfold
            nb078_alpha_dummy_884;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0915
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_857)
        from (by
          unfold
            nb078_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_858 h) from (by
          unfold
            nb078_alpha_dummy_858;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0170 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠
        (nb078_alpha_dummy_854) from (by
          unfold
            nb078_alpha_dummy_854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_856 h) from (by
          unfold
            nb078_alpha_dummy_856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853)
        from (by
          unfold
            nb078_alpha_dummy_853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold
            nb078_alpha_dummy_855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_883)
        from (by
          unfold
            nb078_alpha_dummy_883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_884 h) from (by
          unfold
            nb078_alpha_dummy_884;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0915
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_857)
        from (by
          unfold
            nb078_alpha_dummy_857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_858 h) from (by
          unfold
            nb078_alpha_dummy_858;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0170 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0171 x y h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_890) from (by
          unfold
            nb078_alpha_dummy_890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_892 h) from (by
          unfold
            nb078_alpha_dummy_892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889)
        from (by
          unfold
            nb078_alpha_dummy_889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold
            nb078_alpha_dummy_891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_919)
        from (by
          unfold
            nb078_alpha_dummy_919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_920 h) from (by
          unfold
            nb078_alpha_dummy_920;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0953
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_893)
        from (by
          unfold
            nb078_alpha_dummy_893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_894 h) from (by
          unfold
            nb078_alpha_dummy_894;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0172 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠
        (nb078_alpha_dummy_890) from (by
          unfold
            nb078_alpha_dummy_890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_892 h) from (by
          unfold
            nb078_alpha_dummy_892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889)
        from (by
          unfold
            nb078_alpha_dummy_889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold
            nb078_alpha_dummy_891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_919)
        from (by
          unfold
            nb078_alpha_dummy_919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_920 h) from (by
          unfold
            nb078_alpha_dummy_920;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0953
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_893)
        from (by
          unfold
            nb078_alpha_dummy_893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_894 h) from (by
          unfold
            nb078_alpha_dummy_894;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0172 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)),
        ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049),
        (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_848) from (by
                                        unfold nb078_alpha_dummy_848;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0968)
                                                1)))) (show h ≠ (nb078_alpha_dummy_850 h) from
                                      (by
                                        unfold nb078_alpha_dummy_850;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0969 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_847) from
                                        (by
                                          unfold nb078_alpha_dummy_847;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0968)
                                                  0)))) (show h ≠ (nb078_alpha_dummy_849 h) from
                                        (by
                                          unfold nb078_alpha_dummy_849;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0969 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠
        (nb078_alpha_dummy_851) from (by
          unfold nb078_alpha_dummy_851;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0966) 0)))) (show h ≠ (nb078_alpha_dummy_852 h) from (by
          unfold nb078_alpha_dummy_852;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0967 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1051) from (by
          unfold nb078_alpha_dummy_1051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1260) 2)))) (show h ≠ (nb078_alpha_dummy_1054 h) from (by
          unfold nb078_alpha_dummy_1054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1262 h) 2)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1050) from (by
          unfold nb078_alpha_dummy_1050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1260) 1)))) (show h ≠ (nb078_alpha_dummy_1053 h) from (by
          unfold nb078_alpha_dummy_1053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1262 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1049) from (by
          unfold nb078_alpha_dummy_1049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1260) 0)))) (show h ≠ (nb078_alpha_dummy_1052 h) from (by
          unfold nb078_alpha_dummy_1052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1262 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1055) from (by
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
                  (nb078_support_mem_1263 h)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))

@[expose]
noncomputable def nominal_df_wpp (x : Var) (y : Var) (f : Var) (g : Var) (h : Var)
    (__dv_f_g : f ≠ g) (__dv_f_h : f ≠ h) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y)
    (__dv_g_h : g ≠ h) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_h_x : h ≠ x) (dv_h_y : h ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wwpp) (.all x (.all y (.imp
              (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x)))
                (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))))
              (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y))))))) :=
  by
  change
    Nominal.NPrf
      (Wff.biimp (syn_wwpp) (Wff.all x (Wff.all y (Wff.imp
              (syn_wa (syn_wex f (syn_wfo (Class.cv f) (Class.cv y) (Class.cv x)))
                (syn_wex g (syn_wf1 (Class.cv g) (Class.cv y) (Class.cv x))))
              (syn_wex h (syn_wf1 (Class.cv h) (Class.cv x) (Class.cv y)))))))
  exact
    Nominal.alphaBiimp
      (TAlphaWff.all (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.neg (nb078_split_alpha_0027 x y f dv_f_y))
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_closed
                              [((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)),
                                ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)),
                                ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                ((nb078_alpha_dummy_003), x)]
                              (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078_split_alpha_0029 x y f)))) (TAlphaClass.cv
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_244) from (by
                                    unfold nb078_alpha_dummy_244;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0288) 1))))
                                (show f ≠ (nb078_alpha_dummy_246 f) from (by
                                    unfold nb078_alpha_dummy_246;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0289 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_243) from
                                    (by
                                      unfold nb078_alpha_dummy_243;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0288)
                                              0)))) (show f ≠ (nb078_alpha_dummy_245 f) from (by
                                      unfold nb078_alpha_dummy_245;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0289 f)
                                              0)))) (TAlphaVar.here _ _ _))))))))
                    (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        (Ne.symm dv_f_x) (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.ex
                (TAlphaWff.neg (nb078_split_alpha_0101 x y g dv_g_x dv_g_y dv_x_y))))
            (TAlphaWff.ex
              (TAlphaWff.neg (nb078_split_alpha_0173 x y h dv_h_x dv_h_y dv_x_y))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
