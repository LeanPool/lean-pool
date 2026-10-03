/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block049

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part150`. -/


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
noncomputable def nb078_split_alpha_0128 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
        ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
        ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
        ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
        ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_921))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_921)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_922 h))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_922 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_923) from (by
                                  unfold nb078_alpha_dummy_923;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                              (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_924 h) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0954) 0)))) (show
                                  (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_922 h) from (by
                                    unfold nb078_alpha_dummy_922;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0955 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921),
        (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919),
        (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847),
        (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921),
        (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919),
        (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847),
        (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
                                    ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                                    ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
                                    ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
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
                                    ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                                    ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
                                    ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_890) ≠ (nb078_alpha_dummy_923) from (by
                                  unfold nb078_alpha_dummy_923;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                              (show (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_924 h) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0954) 0)))) (show
                                  (nb078_alpha_dummy_892 h) ≠ (nb078_alpha_dummy_922 h) from (by
                                    unfold nb078_alpha_dummy_922;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0955 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921),
        (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919),
        (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847),
        (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921),
        (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
        ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919),
        (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
        ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847),
        (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
        ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961),
        (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
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
                                    ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                                    ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
                                    ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
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
                                    ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)),
                                    ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
                                    ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
                                    ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
                                    ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
                                    ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
                                    ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
                                    ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
                                    ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
                                    ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
                                    ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)),
            ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)),
            ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
            ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)),
            ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)),
            ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
            ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)),
            ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)),
            ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
            ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
            ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nb078_split_alpha_0129 (x : Var) (y : Var) (h : Var) (dv_h_x : h ≠ x)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (syn_wfun (Class.cv (nb078_alpha_dummy_002))) (Wff.neg
          (Wff.classEq (syn_cdm (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_003)))))
      (Wff.imp (syn_wfun (Class.cv h))
        (Wff.neg (Wff.classEq (syn_cdm (Class.cv h)) (Class.cv x)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0112 x y h))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
                          ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
                          ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                          ((nb078_alpha_dummy_003), x)]
                        (syn_cid) (nb078_wpp_refl_0372 x y h)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0112 x y h))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
                          ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
                          ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                          ((nb078_alpha_dummy_003), x)]
                        (syn_cid) (nb078_wpp_refl_0372 x y h)))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_773) from (by
                          unfold nb078_alpha_dummy_773;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0800) 0))))) (Ne.symm
                      (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_774 h) from (by
                          unfold nb078_alpha_dummy_774;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0801 h) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_773) from (by
                            unfold nb078_alpha_dummy_773;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0798) 0))))) (Ne.symm
                        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_774 h) from (by
                            unfold nb078_alpha_dummy_774;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0799 h) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0113 x y h)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb078_split_alpha_0114 x y h)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb078_split_alpha_0114 x y h))))))))))))) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078_split_alpha_0115 x y h)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_812) from (by
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
                  (nb078_support_mem_0870 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_811)
        from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868)
                  0)))) (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_841)
        from (by
          unfold nb078_alpha_dummy_841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872)
                  0)))) (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_842 h) from (by
          unfold nb078_alpha_dummy_842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_815)
        from (by
          unfold nb078_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869)
                  0)))) (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_816 h) from (by
          unfold nb078_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪
        ((Class.cv (nb078_alpha_dummy_769))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0116 x y h)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_812) from (by
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
                  (nb078_support_mem_0870 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_811)
        from (by
          unfold nb078_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868)
                  0)))) (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_813 h) from (by
          unfold nb078_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_841)
        from (by
          unfold nb078_alpha_dummy_841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872)
                  0)))) (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_842 h) from (by
          unfold nb078_alpha_dummy_842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_815)
        from (by
          unfold nb078_alpha_dummy_815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869)
                  0)))) (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_816 h) from (by
          unfold nb078_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪
        ((Class.cv (nb078_alpha_dummy_769))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_772 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0116 x y h))))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_851) from (by
                                        unfold nb078_alpha_dummy_851;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0880)
                                                0))))) (Ne.symm (show
                                      (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_852 h) from
                                      (by
                                        unfold nb078_alpha_dummy_852;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0881 h)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_851) from
                                        (by
                                          unfold nb078_alpha_dummy_851;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0878)
                                                  0))))) (Ne.symm (show
                                        (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_852 h)
                                        from (by
                                          unfold nb078_alpha_dummy_852;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0879 h) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0117 x y h))))) (TAlphaWff.classMem
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0118 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0118 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854),
        (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)),
        ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857),
        (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0119 x y h))))) (TAlphaWff.classMem
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0120 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0120 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890),
        (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)),
        ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893),
        (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)),
        ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851),
        (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_848) from
                                    (by
                                      unfold nb078_alpha_dummy_848;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0968)
                                              1)))) (show h ≠ (nb078_alpha_dummy_850 h) from (by
                                      unfold nb078_alpha_dummy_850;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0969 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_847) from (by
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
                                              (mem_lt_freshVar (nb078_support_mem_0969 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_851) from
                                        (by
                                          unfold nb078_alpha_dummy_851;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0966)
                                                  0)))) (show h ≠ (nb078_alpha_dummy_852 h) from
                                        (by
                                          unfold nb078_alpha_dummy_852;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0967 h) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_002) ≠
        (nb078_alpha_dummy_769) from (by
          unfold nb078_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0962) 2)))) (show h ≠ (nb078_alpha_dummy_772 h) from (by
          unfold nb078_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0964 h) 2)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_768) from (by
          unfold nb078_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0962) 1)))) (show h ≠ (nb078_alpha_dummy_771 h) from (by
          unfold nb078_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0964 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_767) from (by
          unfold nb078_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0962) 0)))) (show h ≠ (nb078_alpha_dummy_770 h) from (by
          unfold nb078_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0964 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_773) from (by
          unfold nb078_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0963) 0)))) (show h ≠ (nb078_alpha_dummy_774 h) from (by
          unfold nb078_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0965 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078_split_alpha_0121 x y h)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_926) from (by
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
                  (nb078_support_mem_1000 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_925)
        from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998)
                  0)))) (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_955)
        from (by
          unfold nb078_alpha_dummy_955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002)
                  0)))) (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_956 h) from (by
          unfold nb078_alpha_dummy_956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_929)
        from (by
          unfold nb078_alpha_dummy_929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999)
                  0)))) (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_930 h) from (by
          unfold nb078_alpha_dummy_930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv)
        (by decide)) (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_769))).fv ∪
        ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0122 x y h)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_926) from (by
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
                  (nb078_support_mem_1000 h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_925)
        from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998)
                  0)))) (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_955)
        from (by
          unfold nb078_alpha_dummy_955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002)
                  0)))) (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_956 h) from (by
          unfold nb078_alpha_dummy_956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_929)
        from (by
          unfold nb078_alpha_dummy_929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999)
                  0)))) (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_930 h) from (by
          unfold nb078_alpha_dummy_930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv)
        (by decide)) (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_769))).fv ∪
        ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0122 x y h))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.there
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
                                  (mem_lt_freshVar (nb078_support_mem_0964 h) 2))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_768) from (by
                              unfold nb078_alpha_dummy_768;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0962) 1))))
                          (show h ≠ (nb078_alpha_dummy_771 h) from (by
                              unfold nb078_alpha_dummy_771;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0964 h) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_767) from (by
                                unfold nb078_alpha_dummy_767;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0962) 0))))
                            (show h ≠ (nb078_alpha_dummy_770 h) from (by
                                unfold nb078_alpha_dummy_770;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0964 h) 0))))
                            (TAlphaVar.there
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
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)),
                    ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)),
                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_cvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0124 x y h))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                                (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_851) from (by
                                    unfold nb078_alpha_dummy_851;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0880) 0)))))
                              (Ne.symm (show
                                  (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_852 h) from (by
                                    unfold nb078_alpha_dummy_852;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0881 h)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_851) from
                                    (by
                                      unfold nb078_alpha_dummy_851;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0878)
                                              0))))) (Ne.symm (show
                                    (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_852 h) from
                                    (by
                                      unfold nb078_alpha_dummy_852;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0879 h)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078_split_alpha_0125 x y h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0912
                    h)
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0126 x y h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0912
                    h)
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0126 x y h))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078_split_alpha_0127 x y h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0950
                    h)
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0128 x y h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0950
                    h)
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0128 x y h)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
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
                                          (mem_lt_freshVar (nb078_support_mem_0969 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_851) from
                                    (by
                                      unfold nb078_alpha_dummy_851;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0966)
                                              0)))) (show h ≠ (nb078_alpha_dummy_852 h) from (by
                                      unfold nb078_alpha_dummy_852;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0967 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_962) from (by
                                        unfold nb078_alpha_dummy_962;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1046)
                                                1)))) (show h ≠ (nb078_alpha_dummy_964 h) from
                                      (by
                                        unfold nb078_alpha_dummy_964;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1047 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_961) from
                                        (by
                                          unfold nb078_alpha_dummy_961;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1046)
                                                  0)))) (show h ≠ (nb078_alpha_dummy_963 h) from
                                        (by
                                          unfold nb078_alpha_dummy_963;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1047 h) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_h_x)
            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
              (TAlphaVar.here _ _ _)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part151`. -/


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
noncomputable def nb078_split_alpha_0130 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
        ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
        ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
        ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1015))
          (Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1015)) (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1016 h))
          (Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_1016 h))
            (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1010) from
                    (by
                      unfold nb078_alpha_dummy_1010;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                  (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1012 h) from (by
                      unfold nb078_alpha_dummy_1012;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1009) from (by
                        unfold nb078_alpha_dummy_1009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                    (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1011 h) from (by
                        unfold nb078_alpha_dummy_1011;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1050 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1015) from (by
                          unfold nb078_alpha_dummy_1015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1052) 0))))
                      (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1016 h) from (by
                          unfold nb078_alpha_dummy_1016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1013) from (by
                            unfold nb078_alpha_dummy_1013;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1049) 0))))
                        (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1014 h) from (by
                            unfold nb078_alpha_dummy_1014;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1051 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1006))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from (by
                              unfold nb078_alpha_dummy_1017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                          (show (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1019 h) from (by
                              unfold nb078_alpha_dummy_1019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from (by
                                unfold nb078_alpha_dummy_1018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 1))))
                            (show (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1020 h) from
                              (by
                                unfold nb078_alpha_dummy_1020;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_1012 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001),
        (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001),
        (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                      (by
                                        unfold nb078_alpha_dummy_1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                        (nb078_alpha_dummy_1022 h) from (by
                                        unfold nb078_alpha_dummy_1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                    ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                    ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                    ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                    ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                    ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
                                    ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                    ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from (by
                                      unfold nb078_alpha_dummy_1021;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1056)
                                              0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                      (nb078_alpha_dummy_1022 h) from (by
                                      unfold nb078_alpha_dummy_1022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1057 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                      (by
                                        unfold nb078_alpha_dummy_1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                        (nb078_alpha_dummy_1022 h) from (by
                                        unfold nb078_alpha_dummy_1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                    ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                    ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                    ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                    ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                    ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
                                    ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                    ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                    ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                    ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                    ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1010) from (by
                        unfold nb078_alpha_dummy_1010;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                    (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1012 h) from (by
                        unfold nb078_alpha_dummy_1012;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1050 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1009) from (by
                          unfold nb078_alpha_dummy_1009;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                      (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1011 h) from (by
                          unfold nb078_alpha_dummy_1011;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1015) from (by
                            unfold nb078_alpha_dummy_1015;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1052) 0))))
                        (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1016 h) from (by
                            unfold nb078_alpha_dummy_1016;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1013) from (by
                              unfold nb078_alpha_dummy_1013;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1049) 0))))
                          (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1014 h) from (by
                              unfold nb078_alpha_dummy_1014;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1051 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_1006))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1017) from (by
                                unfold nb078_alpha_dummy_1017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                            (show (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1019 h) from
                              (by
                                unfold nb078_alpha_dummy_1019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_1010) ≠ (nb078_alpha_dummy_1018) from (by
                                  unfold nb078_alpha_dummy_1018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1054) 1)))) (show
                                (nb078_alpha_dummy_1012 h) ≠ (nb078_alpha_dummy_1020 h) from (by
                                  unfold nb078_alpha_dummy_1020;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1024) from (by
          unfold nb078_alpha_dummy_1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1027 h) from (by
          unfold nb078_alpha_dummy_1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1023) from (by
          unfold nb078_alpha_dummy_1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1026 h) from (by
          unfold nb078_alpha_dummy_1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1017) ≠
        (nb078_alpha_dummy_1021) from (by
          unfold nb078_alpha_dummy_1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078_alpha_dummy_1019 h) ≠ (nb078_alpha_dummy_1022 h) from (by
          unfold nb078_alpha_dummy_1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001),
        (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1031) from (by
          unfold
            nb078_alpha_dummy_1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1032 h) from (by
          unfold
            nb078_alpha_dummy_1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1029) from (by
          unfold
            nb078_alpha_dummy_1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1030 h) from (by
          unfold
            nb078_alpha_dummy_1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024),
        (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)),
        ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017),
        (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
        ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009),
        (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
        ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006),
        (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
        ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001),
        (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1024) ≠ (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1035) from (by
          unfold
            nb078_alpha_dummy_1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1036 h) from (by
          unfold
            nb078_alpha_dummy_1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1024) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078_alpha_dummy_1027 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_1025) ≠ (nb078_alpha_dummy_1037) from (by
          unfold
            nb078_alpha_dummy_1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1038 h) from (by
          unfold
            nb078_alpha_dummy_1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_1025) ≠
        (nb078_alpha_dummy_1033) from (by
          unfold
            nb078_alpha_dummy_1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078_alpha_dummy_1028 h) ≠ (nb078_alpha_dummy_1034 h) from (by
          unfold
            nb078_alpha_dummy_1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                        (by
                                          unfold nb078_alpha_dummy_1021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1056)
                                                  0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
                                          unfold nb078_alpha_dummy_1022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1057 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                      ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                      ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                      ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                      ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                      ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
                                      ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                      ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                      ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                      ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                      ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                      (by
                                        unfold nb078_alpha_dummy_1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078_alpha_dummy_1019 h) ≠
                                        (nb078_alpha_dummy_1022 h) from (by
                                        unfold nb078_alpha_dummy_1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1021) from
                                        (by
                                          unfold nb078_alpha_dummy_1021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1056)
                                                  0)))) (show (nb078_alpha_dummy_1019 h) ≠
        (nb078_alpha_dummy_1022 h) from (by
                                          unfold nb078_alpha_dummy_1022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1057 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)),
                                      ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)),
                                      ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)),
                                      ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)),
                                      ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)),
                                      ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)),
                                      ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)),
                                      ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)),
                                      ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)),
                                      ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)),
                                      ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
