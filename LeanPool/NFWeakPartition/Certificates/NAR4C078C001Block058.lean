/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block057

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part170`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0151`. -/
@[expose]
noncomputable def nb078SplitAlpha0151 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy895))
          (Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy895)) (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCphi (Class.cv (nb078AlphaDummy890)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy896 h))
          (Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy896 h))
            (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCphi (Class.cv (nb078AlphaDummy892 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy890) from
                    (by
                      unfold nb078AlphaDummy890;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                  (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy892 h) from (by
                      unfold nb078AlphaDummy892;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy889) from
                      (by
                        unfold nb078AlphaDummy889;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                    (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy891 h) from (by
                        unfold nb078AlphaDummy891;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy895) from (by
                          unfold nb078AlphaDummy895;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy896 h) from (by
                          unfold nb078AlphaDummy896;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy893) from (by
                            unfold nb078AlphaDummy893;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy894 h) from (by
                            unfold nb078AlphaDummy894;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy848))).fv ∪
                      ((Class.cv (nb078AlphaDummy847))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy850 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy849 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy897) from (by
                              unfold nb078AlphaDummy897;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                          (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy899 h) from (by
                              unfold nb078AlphaDummy899;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy898) from (by
                                unfold nb078AlphaDummy898;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                            (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy900 h) from (by
                                unfold nb078AlphaDummy900;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy890))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy892 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy904) from (by
          unfold nb078AlphaDummy904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy907 h) from (by
          unfold nb078AlphaDummy907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy903) from (by
          unfold nb078AlphaDummy903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy906 h) from (by
          unfold nb078AlphaDummy906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
          unfold nb078AlphaDummy901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
          unfold nb078AlphaDummy902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy915) from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915)
        from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠
        (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                        unfold nb078AlphaDummy901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078AlphaDummy899 h) ≠
                                        (nb078AlphaDummy902 h) from (by
                                        unfold nb078AlphaDummy902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                    ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                    ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from
                                    (by
                                      unfold nb078AlphaDummy901;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0928)
                                              0)))) (show
                                    (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from
                                    (by
                                      unfold nb078AlphaDummy902;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0929 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                        unfold nb078AlphaDummy901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078AlphaDummy899 h) ≠
                                        (nb078AlphaDummy902 h) from (by
                                        unfold nb078AlphaDummy902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                    ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                    ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                    ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy890) from
                      (by
                        unfold nb078AlphaDummy890;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
                    (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy892 h) from (by
                        unfold nb078AlphaDummy892;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0922 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy889) from (by
                          unfold nb078AlphaDummy889;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0920) 0))))
                      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy891 h) from (by
                          unfold nb078AlphaDummy891;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy895) from (by
                            unfold nb078AlphaDummy895;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0924) 0))))
                        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy896 h) from (by
                            unfold nb078AlphaDummy896;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0925 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy893) from (by
                              unfold nb078AlphaDummy893;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0921) 0))))
                          (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy894 h) from (by
                              unfold nb078AlphaDummy894;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0923 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy848))).fv ∪
                        ((Class.cv (nb078AlphaDummy847))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy850 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy849 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy897) from (by
                                unfold nb078AlphaDummy897;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                            (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy899 h) from (by
                                unfold nb078AlphaDummy899;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy898) from (by
                                  unfold nb078AlphaDummy898;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                              (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy900 h) from
                                (by
                                  unfold nb078AlphaDummy900;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy890))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy892 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy904) from (by
          unfold nb078AlphaDummy904;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 1)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy907 h) from (by
          unfold nb078AlphaDummy907;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy903) from (by
          unfold nb078AlphaDummy903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy906 h) from (by
          unfold nb078AlphaDummy906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901)
        from (by
          unfold nb078AlphaDummy901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928)
                  0)))) (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from (by
          unfold nb078AlphaDummy902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy899
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy915) from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915)
        from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠
        (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from
                                        (by
                                          unfold nb078AlphaDummy901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
                                          unfold nb078AlphaDummy902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                      ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                      ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                      ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                      ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                      ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                      ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                        unfold nb078AlphaDummy901;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0928)
                                                0)))) (show (nb078AlphaDummy899 h) ≠
                                        (nb078AlphaDummy902 h) from (by
                                        unfold nb078AlphaDummy902;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0929 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from
                                        (by
                                          unfold nb078AlphaDummy901;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0928)
                                                  0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
                                          unfold nb078AlphaDummy902;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0929 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                      ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                      ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                      ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                      ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                      ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                      ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                      ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                      ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                      ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                      ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part171`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0152`. -/
@[expose]
noncomputable def nb078SplitAlpha0152 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
        ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy923))
          (synCphi (Class.cv (nb078AlphaDummy890)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy923))
            (synCphi (Class.cv (nb078AlphaDummy890))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy924 h))
          (synCphi (Class.cv (nb078AlphaDummy892 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy924 h))
            (synCphi (Class.cv (nb078AlphaDummy892 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy897) from
                    (by
                      unfold nb078AlphaDummy897;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                  (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy899 h) from (by
                      unfold nb078AlphaDummy899;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0927 h) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy898) from
                      (by
                        unfold nb078AlphaDummy898;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                    (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy900 h) from (by
                        unfold nb078AlphaDummy900;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0927 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy923) from (by
                          unfold nb078AlphaDummy923;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                      (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy924 h) from (by
                          unfold nb078AlphaDummy924;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0957 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy921) from (by
                            unfold nb078AlphaDummy921;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0954) 0))))
                        (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy922 h) from (by
                            unfold nb078AlphaDummy922;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0955 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy890))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy892 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy897) ≠ (nb078AlphaDummy904) from (by
                                        unfold nb078AlphaDummy904;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0930)
                                                1)))) (show (nb078AlphaDummy899 h) ≠
                                        (nb078AlphaDummy907 h) from (by
                                        unfold nb078AlphaDummy907;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0931 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy897) ≠ (nb078AlphaDummy903) from
                                        (by
                                          unfold nb078AlphaDummy903;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0930)
                                                  0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy906 h) from (by
                                          unfold nb078AlphaDummy906;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0931 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy897) ≠
        (nb078AlphaDummy901) from (by
          unfold nb078AlphaDummy901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
          unfold nb078AlphaDummy902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy905),
        (nb078AlphaDummy908 h)), ((nb078AlphaDummy904), (nb078AlphaDummy907 h)),
                                        ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
                                        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                                        ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                                        ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                                        ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                                        ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                                        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                                        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                                        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                                        ((nb078AlphaDummy002), h),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)),
        ((nb078AlphaDummy904), (nb078AlphaDummy907 h)), ((nb078AlphaDummy903),
        (nb078AlphaDummy906 h)), ((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
        ((nb078AlphaDummy897), (nb078AlphaDummy899 h)), ((nb078AlphaDummy898),
        (nb078AlphaDummy900 h)), ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
        ((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy915) from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915)
        from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠
        (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                unfold nb078AlphaDummy901;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                            (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from (by
                                unfold nb078AlphaDummy902;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                            ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                            ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                            ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                            ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                            ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                            ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                            ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                            ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                              unfold nb078AlphaDummy901;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                          (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from (by
                              unfold nb078AlphaDummy902;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                unfold nb078AlphaDummy901;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                            (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from (by
                                unfold nb078AlphaDummy902;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                            ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                            ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                            ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                            ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                            ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                            ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                            ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                            ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                            ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                            ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy897) from (by
                        unfold nb078AlphaDummy897;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 0))))
                    (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy899 h) from (by
                        unfold nb078AlphaDummy899;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0927 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy898) from (by
                          unfold nb078AlphaDummy898;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0926) 1))))
                      (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy900 h) from (by
                          unfold nb078AlphaDummy900;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0927 h) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy923) from (by
                            unfold nb078AlphaDummy923;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                        (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy924 h) from (by
                            unfold nb078AlphaDummy924;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0957 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy921) from (by
                              unfold nb078AlphaDummy921;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0954) 0))))
                          (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy922 h) from (by
                              unfold nb078AlphaDummy922;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0955 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy890))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy892 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy897) ≠ (nb078AlphaDummy904) from
                                        (by
                                          unfold nb078AlphaDummy904;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0930)
                                                  1)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy907 h) from (by
                                          unfold nb078AlphaDummy907;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0931 h) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy897) ≠
        (nb078AlphaDummy903) from (by
          unfold nb078AlphaDummy903;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0930) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy906 h) from (by
          unfold nb078AlphaDummy906;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0931 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
          unfold nb078AlphaDummy901;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0928) 0)))) (show (nb078AlphaDummy899 h) ≠
        (nb078AlphaDummy902 h) from (by
          unfold nb078AlphaDummy902;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0929 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy905),
        (nb078AlphaDummy908 h)), ((nb078AlphaDummy904), (nb078AlphaDummy907 h)),
        ((nb078AlphaDummy903), (nb078AlphaDummy906 h)), ((nb078AlphaDummy901),
        (nb078AlphaDummy902 h)), ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
        ((nb078AlphaDummy898), (nb078AlphaDummy900 h)), ((nb078AlphaDummy923),
        (nb078AlphaDummy924 h)), ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy911) from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0934)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0935
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0932)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0933
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy911)
        from (by
          unfold
            nb078AlphaDummy911;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0938)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy912 h) from (by
          unfold
            nb078AlphaDummy912;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0939
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy909)
        from (by
          unfold
            nb078AlphaDummy909;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0936)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy910 h) from (by
          unfold
            nb078AlphaDummy910;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0937
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy905), (nb078AlphaDummy908 h)), ((nb078AlphaDummy904),
        (nb078AlphaDummy907 h)), ((nb078AlphaDummy903), (nb078AlphaDummy906 h)),
        ((nb078AlphaDummy901), (nb078AlphaDummy902 h)), ((nb078AlphaDummy897),
        (nb078AlphaDummy899 h)), ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
        ((nb078AlphaDummy923), (nb078AlphaDummy924 h)), ((nb078AlphaDummy921),
        (nb078AlphaDummy922 h)), ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)), ((nb078AlphaDummy919),
        (nb078AlphaDummy920 h)), ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy1047),
        (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠
        (nb078AlphaDummy915) from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915)
        from (by
          unfold
            nb078AlphaDummy915;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0942)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy916 h) from (by
          unfold
            nb078AlphaDummy916;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0943
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0940)
                  0)))) (show (nb078AlphaDummy907 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0941
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy905) ≠
        (nb078AlphaDummy917) from (by
          unfold
            nb078AlphaDummy917;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0946)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy918 h) from (by
          unfold
            nb078AlphaDummy918;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0947
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy905) ≠ (nb078AlphaDummy913)
        from (by
          unfold
            nb078AlphaDummy913;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0944)
                  0)))) (show (nb078AlphaDummy908 h) ≠ (nb078AlphaDummy914 h) from (by
          unfold
            nb078AlphaDummy914;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0945
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                  unfold nb078AlphaDummy901;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                              (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from
                                (by
                                  unfold nb078AlphaDummy902;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                              ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                              ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                              ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                              ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                              ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                              ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                              ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                              ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                              ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                unfold nb078AlphaDummy901;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                            (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from (by
                                unfold nb078AlphaDummy902;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy897) ≠ (nb078AlphaDummy901) from (by
                                  unfold nb078AlphaDummy901;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0928) 0))))
                              (show (nb078AlphaDummy899 h) ≠ (nb078AlphaDummy902 h) from
                                (by
                                  unfold nb078AlphaDummy902;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0929 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy901), (nb078AlphaDummy902 h)),
                              ((nb078AlphaDummy897), (nb078AlphaDummy899 h)),
                              ((nb078AlphaDummy898), (nb078AlphaDummy900 h)),
                              ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                              ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                              ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                              ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                              ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                              ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                              ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                              ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                              ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
                              ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0153`. -/
@[expose]
noncomputable def nb078SplitAlpha0153 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)),
        ((nb078AlphaDummy1045), (nb078AlphaDummy1046 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy1055))
          (synCop (Class.cv (nb078AlphaDummy1049)) (Class.cv (nb078AlphaDummy1050))))
        (Wff.neg (synWex (nb078AlphaDummy1051) (synWa
              (synWbr (Class.cv (nb078AlphaDummy1049))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))
                (Class.cv (nb078AlphaDummy1051)))
              (synWbr (Class.cv (nb078AlphaDummy1051))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy1050)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078AlphaDummy1056 h))
          (synCop (Class.cv (nb078AlphaDummy1052 h)) (Class.cv (nb078AlphaDummy1053 h))))
        (Wff.neg (synWex (nb078AlphaDummy1054 h) (synWa
              (synWbr (Class.cv (nb078AlphaDummy1052 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb078AlphaDummy1054 h)))
              (synWbr (Class.cv (nb078AlphaDummy1054 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy1053 h))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1055) from (by
                unfold nb078AlphaDummy1055;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1098) 0))))) (Ne.symm
            (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1056 h) from (by
                unfold nb078AlphaDummy1056;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1099 h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1055) from (by
                  unfold nb078AlphaDummy1055;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1096) 0)))))
            (Ne.symm (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1056 h) from (by
                  unfold nb078AlphaDummy1056;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1097 h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0134 x y h)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1058) from (by
                                      unfold nb078AlphaDummy1058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1128)
                                              1)))) (show (nb078AlphaDummy1053 h) ≠
                                      (nb078AlphaDummy1060 h) from (by
                                      unfold nb078AlphaDummy1060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1130 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1057) from
                                      (by
                                        unfold nb078AlphaDummy1057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1128)
                                                0)))) (show (nb078AlphaDummy1053 h) ≠
                                        (nb078AlphaDummy1059 h) from (by
                                        unfold nb078AlphaDummy1059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1130 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1087) from
                                        (by
                                          unfold nb078AlphaDummy1087;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1132)
                                                  0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1088 h) from (by
                                          unfold nb078AlphaDummy1088;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1133 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1050) ≠
        (nb078AlphaDummy1061) from (by
          unfold nb078AlphaDummy1061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1129) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1062 h) from (by
          unfold nb078AlphaDummy1062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1131 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy1049))).fv ∪
                                      ((Class.cv (nb078AlphaDummy1050))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                                      ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0135 x y h)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1058) from (by
                                      unfold nb078AlphaDummy1058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1128)
                                              1)))) (show (nb078AlphaDummy1053 h) ≠
                                      (nb078AlphaDummy1060 h) from (by
                                      unfold nb078AlphaDummy1060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1130 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1057) from
                                      (by
                                        unfold nb078AlphaDummy1057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1128)
                                                0)))) (show (nb078AlphaDummy1053 h) ≠
                                        (nb078AlphaDummy1059 h) from (by
                                        unfold nb078AlphaDummy1059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1130 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1087) from
                                        (by
                                          unfold nb078AlphaDummy1087;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1132)
                                                  0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1088 h) from (by
                                          unfold nb078AlphaDummy1088;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1133 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy1050) ≠
        (nb078AlphaDummy1061) from (by
          unfold nb078AlphaDummy1061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1129) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1062 h) from (by
          unfold nb078AlphaDummy1062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1131 h) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy1049))).fv ∪
                                      ((Class.cv (nb078AlphaDummy1050))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                                      ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0135 x y h)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0136 x y h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy1051) ≠
        (nb078AlphaDummy1094) from (by
          unfold nb078AlphaDummy1094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1166) 1)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1096 h) from (by
          unfold nb078AlphaDummy1096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1168 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1093) from (by
          unfold nb078AlphaDummy1093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1166) 0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1095 h) from (by
          unfold nb078AlphaDummy1095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1168 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1123) from (by
          unfold nb078AlphaDummy1123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1170) 0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1124 h) from (by
          unfold nb078AlphaDummy1124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1171 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1097) from (by
          unfold nb078AlphaDummy1097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1167) 0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1098 h) from (by
          unfold nb078AlphaDummy1098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1169 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1054 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0137 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)), ((nb078AlphaDummy1094),
        (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
        ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)), ((nb078AlphaDummy1097),
        (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy1051) ≠
        (nb078AlphaDummy1094) from (by
          unfold nb078AlphaDummy1094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1166) 1)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1096 h) from (by
          unfold nb078AlphaDummy1096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1168 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1093) from (by
          unfold nb078AlphaDummy1093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1166) 0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1095 h) from (by
          unfold nb078AlphaDummy1095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1168 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1123) from (by
          unfold nb078AlphaDummy1123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1170) 0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1124 h) from (by
          unfold nb078AlphaDummy1124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1171 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1097) from (by
          unfold nb078AlphaDummy1097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1167) 0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1098 h) from (by
          unfold nb078AlphaDummy1098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1169 h) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1054 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0137 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1125), (nb078AlphaDummy1126 h)), ((nb078AlphaDummy1094),
        (nb078AlphaDummy1096 h)), ((nb078AlphaDummy1093), (nb078AlphaDummy1095 h)),
        ((nb078AlphaDummy1123), (nb078AlphaDummy1124 h)), ((nb078AlphaDummy1097),
        (nb078AlphaDummy1098 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0146 x y h))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0147 x y h)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy1050) ≠
        (nb078AlphaDummy1208) from (by
          unfold nb078AlphaDummy1208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296) 1)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1210 h) from (by
          unfold nb078AlphaDummy1210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1207) from (by
          unfold nb078AlphaDummy1207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1209 h) from (by
          unfold nb078AlphaDummy1209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1237) from (by
          unfold nb078AlphaDummy1237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1300) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1238 h) from (by
          unfold nb078AlphaDummy1238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1301 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1211) from (by
          unfold nb078AlphaDummy1211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1297) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1212 h) from (by
          unfold nb078AlphaDummy1212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1299 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb078AlphaDummy002))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0148 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)), ((nb078AlphaDummy1208),
        (nb078AlphaDummy1210 h)), ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
        ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)), ((nb078AlphaDummy1211),
        (nb078AlphaDummy1212 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078AlphaDummy1050) ≠
        (nb078AlphaDummy1208) from (by
          unfold nb078AlphaDummy1208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296) 1)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1210 h) from (by
          unfold nb078AlphaDummy1210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1207) from (by
          unfold nb078AlphaDummy1207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1296) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1209 h) from (by
          unfold nb078AlphaDummy1209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1298 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1237) from (by
          unfold nb078AlphaDummy1237;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1300) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1238 h) from (by
          unfold nb078AlphaDummy1238;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1301 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1211) from (by
          unfold nb078AlphaDummy1211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1297) 0)))) (show (nb078AlphaDummy1053 h) ≠
        (nb078AlphaDummy1212 h) from (by
          unfold nb078AlphaDummy1212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1299 h) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb078AlphaDummy002))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0148 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1239), (nb078AlphaDummy1240 h)), ((nb078AlphaDummy1208),
        (nb078AlphaDummy1210 h)), ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
        ((nb078AlphaDummy1237), (nb078AlphaDummy1238 h)), ((nb078AlphaDummy1211),
        (nb078AlphaDummy1212 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
                                  (TAlphaWff.neg (nb078SplitAlpha0149 x y h)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0150 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0150 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078SplitAlpha0151 x y h)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0152 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0152 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy1047), (nb078AlphaDummy1048 h)), ((nb078AlphaDummy1045),
        (nb078AlphaDummy1046 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
                                (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy1051) from
                                  (by
                                    unfold nb078AlphaDummy1051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1260) 2))))
                                (show h ≠ (nb078AlphaDummy1054 h) from (by
                                    unfold nb078AlphaDummy1054;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1262 h)
                                            2)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy1050) from
                                    (by
                                      unfold nb078AlphaDummy1050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1260)
                                              1)))) (show h ≠ (nb078AlphaDummy1053 h) from
                                    (by
                                      unfold nb078AlphaDummy1053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1262 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy002) ≠ (nb078AlphaDummy1049) from
                                      (by
                                        unfold nb078AlphaDummy1049;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1260)
                                                0)))) (show h ≠ (nb078AlphaDummy1052 h) from
                                      (by
                                        unfold nb078AlphaDummy1052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1262 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy002) ≠ (nb078AlphaDummy1055) from
                                        (by
                                          unfold nb078AlphaDummy1055;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1261)
                                                  0))))
                                      (show h ≠ (nb078AlphaDummy1056 h) from (by
                                          unfold nb078AlphaDummy1056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1263 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy002) ≠
        (nb078AlphaDummy1047) from (by
          unfold nb078AlphaDummy1047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1258) 0)))) (show h ≠ (nb078AlphaDummy1048 h) from (by
          unfold nb078AlphaDummy1048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1259 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy1045) from (by
          unfold nb078AlphaDummy1045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1256) 0)))) (show h ≠ (nb078AlphaDummy1046 h) from (by
          unfold nb078AlphaDummy1046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1257 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))

theorem nb078_wpp_notmem_3138 : (nb078AlphaDummy1047) ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0816)

theorem nb078_wpp_notmem_3139 (h : Var) : (nb078AlphaDummy1048 h) ∉ ((synCid)).fv :=
  by simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0817 h)

theorem nb078_wpp_notmem_3140 : (nb078AlphaDummy1045) ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0818)

theorem nb078_wpp_notmem_3141 (h : Var) : (nb078AlphaDummy1046 h) ∉ ((synCid)).fv :=
  by simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0819 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
