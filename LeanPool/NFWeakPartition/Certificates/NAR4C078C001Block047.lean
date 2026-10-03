/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block046

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part141`. -/


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
noncomputable def nb078_split_alpha_0119 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part142`. -/


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
noncomputable def nb078_split_alpha_0120 (x : Var) (y : Var) (h : Var) :
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
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
                                        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
                            ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                            ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                            ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                            ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
                            ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                            ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                            ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                            ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
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
                              ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                              ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                              ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                              ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
                              ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                              ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                              ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                              ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                              ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part143`. -/


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
noncomputable def nb078_split_alpha_0121 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
        ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_931))
          (Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_931)) (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_932 h))
          (Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_932 h))
            (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_926) from
                    (by
                      unfold nb078_alpha_dummy_926;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
                  (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_928 h) from (by
                      unfold nb078_alpha_dummy_928;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_925) from
                      (by
                        unfold nb078_alpha_dummy_925;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))))
                    (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_927 h) from (by
                        unfold nb078_alpha_dummy_927;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0972 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_931) from (by
                          unfold nb078_alpha_dummy_931;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0974) 0))))
                      (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_932 h) from (by
                          unfold nb078_alpha_dummy_932;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0975 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_929) from (by
                            unfold nb078_alpha_dummy_929;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0971) 0))))
                        (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_930 h) from (by
                            unfold nb078_alpha_dummy_930;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0973 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_769))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_928 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_933) ≠ (nb078_alpha_dummy_940) from (by
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
                  (nb078_support_mem_0979 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940),
        (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)),
        ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933),
        (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
        ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925),
        (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
        ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925),
        (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
        ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)),
                                    ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)),
                                    ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
                                    ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                    ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                    ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
                                    ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
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
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)),
                                    ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)),
                                    ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)),
                                    ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                    ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                    ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
                                    ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_926) from
                      (by
                        unfold nb078_alpha_dummy_926;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
                    (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_928 h) from (by
                        unfold nb078_alpha_dummy_928;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0972 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_925) from (by
                          unfold nb078_alpha_dummy_925;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0970) 0))))
                      (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_927 h) from (by
                          unfold nb078_alpha_dummy_927;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0972 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_931) from (by
                            unfold nb078_alpha_dummy_931;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0974) 0))))
                        (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_932 h) from (by
                            unfold nb078_alpha_dummy_932;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0975 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_929) from (by
                              unfold nb078_alpha_dummy_929;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0971) 0))))
                          (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_930 h) from (by
                              unfold nb078_alpha_dummy_930;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0973 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_769))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
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
        ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925),
        (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
        ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925),
        (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
        ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                      ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                      ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                      ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
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
                                      ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)),
                                      ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)),
                                      ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)),
                                      ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
