/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block062

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part183`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0165`. -/
@[expose]
noncomputable def nb078SplitAlpha0165 (x : Var) (y : Var) (h : Var) :
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
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
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
                                        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                                        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                                        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                                        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
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
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
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
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
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
                            ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                            ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                            ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                            ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                            ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                            ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                            ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130),
        (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
        ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
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
        ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)), ((nb078AlphaDummy1129),
        (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050),
        (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
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
                              ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
                              ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)),
                              ((nb078AlphaDummy1133), (nb078AlphaDummy1134 h)),
                              ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                              ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                              ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                              ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0166`. -/
@[expose]
noncomputable def nb078SplitAlpha0166 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.classMem
        (synCop (Class.cv (nb078AlphaDummy1049)) (Class.cv (nb078AlphaDummy1051)))
        (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002)))))
      (Wff.classMem (synCop (Class.cv (nb078AlphaDummy1052 h))
          (Class.cv (nb078AlphaDummy1054 h))) (synCcnv (synCcnv (Class.cv h)))) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0156 x y h)))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1094) from
                                  (by
                                    unfold nb078AlphaDummy1094;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1166) 1)))) (show
                                  (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1096 h) from
                                  (by
                                    unfold nb078AlphaDummy1096;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1168 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1093) from (by
                                      unfold nb078AlphaDummy1093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1166)
                                              0)))) (show (nb078AlphaDummy1054 h) ≠
                                      (nb078AlphaDummy1095 h) from (by
                                      unfold nb078AlphaDummy1095;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1168 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1123) from
                                      (by
                                        unfold nb078AlphaDummy1123;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1170)
                                                0)))) (show (nb078AlphaDummy1054 h) ≠
                                        (nb078AlphaDummy1124 h) from (by
                                        unfold nb078AlphaDummy1124;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1171 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1097) from
                                        (by
                                          unfold nb078AlphaDummy1097;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1167)
                                                  0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1098 h) from (by
                                          unfold nb078AlphaDummy1098;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1169 h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb078AlphaDummy1049))).fv ∪
                                    ((Class.cv (nb078AlphaDummy1051))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                                    ((Class.cv (nb078AlphaDummy1054 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0157 x y h)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1094) from
                                  (by
                                    unfold nb078AlphaDummy1094;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1166) 1)))) (show
                                  (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1096 h) from
                                  (by
                                    unfold nb078AlphaDummy1096;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_1168 h)
                                            1)))) (TAlphaVar.there (show
                                    (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1093) from (by
                                      unfold nb078AlphaDummy1093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1166)
                                              0)))) (show (nb078AlphaDummy1054 h) ≠
                                      (nb078AlphaDummy1095 h) from (by
                                      unfold nb078AlphaDummy1095;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1168 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1123) from
                                      (by
                                        unfold nb078AlphaDummy1123;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1170)
                                                0)))) (show (nb078AlphaDummy1054 h) ≠
                                        (nb078AlphaDummy1124 h) from (by
                                        unfold nb078AlphaDummy1124;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1171 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1097) from
                                        (by
                                          unfold nb078AlphaDummy1097;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1167)
                                                  0)))) (show (nb078AlphaDummy1054 h) ≠
        (nb078AlphaDummy1098 h) from (by
                                          unfold nb078AlphaDummy1098;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1169 h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb078AlphaDummy1049))).fv ∪
                                    ((Class.cv (nb078AlphaDummy1051))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
                                    ((Class.cv (nb078AlphaDummy1054 h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0157 x y h))))))))))))))))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                    (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1133) from (by
                        unfold nb078AlphaDummy1133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1178) 0)))))
                  (Ne.symm (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1134 h) from
                      (by
                        unfold nb078AlphaDummy1134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1179 h) 0)))))
                  (TAlphaVar.there (Ne.symm
                      (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1133) from (by
                          unfold nb078AlphaDummy1133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1176) 0))))) (Ne.symm
                      (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1134 h) from (by
                          unfold nb078AlphaDummy1134;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1177 h) 0)))))
                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0158 x y h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy1130) ≠
        (nb078AlphaDummy1136) from (by
          unfold nb078AlphaDummy1136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1208) 1)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1138 h) from (by
          unfold nb078AlphaDummy1138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1210 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1135) from (by
          unfold nb078AlphaDummy1135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1208) 0)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1137 h) from (by
          unfold nb078AlphaDummy1137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1210 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1165) from (by
          unfold nb078AlphaDummy1165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1212) 0)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1166 h) from (by
          unfold nb078AlphaDummy1166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1213 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1139) from (by
          unfold nb078AlphaDummy1139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1209) 0)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1140 h) from (by
          unfold nb078AlphaDummy1140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1211 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1132 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0159 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)), ((nb078AlphaDummy1136),
        (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
        ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)), ((nb078AlphaDummy1139),
        (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy1130) ≠
        (nb078AlphaDummy1136) from (by
          unfold nb078AlphaDummy1136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1208) 1)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1138 h) from (by
          unfold nb078AlphaDummy1138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1210 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1135) from (by
          unfold nb078AlphaDummy1135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1208) 0)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1137 h) from (by
          unfold nb078AlphaDummy1137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1210 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1165) from (by
          unfold nb078AlphaDummy1165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1212) 0)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1166 h) from (by
          unfold nb078AlphaDummy1166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1213 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1139) from (by
          unfold nb078AlphaDummy1139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1209) 0)))) (show (nb078AlphaDummy1132 h) ≠
        (nb078AlphaDummy1140 h) from (by
          unfold nb078AlphaDummy1140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1211 h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1132 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0159 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1167), (nb078AlphaDummy1168 h)), ((nb078AlphaDummy1136),
        (nb078AlphaDummy1138 h)), ((nb078AlphaDummy1135), (nb078AlphaDummy1137 h)),
        ((nb078AlphaDummy1165), (nb078AlphaDummy1166 h)), ((nb078AlphaDummy1139),
        (nb078AlphaDummy1140 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0160 x y h)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy1129) ≠
        (nb078AlphaDummy1172) from (by
          unfold nb078AlphaDummy1172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1246) 1)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1174 h) from (by
          unfold nb078AlphaDummy1174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1248 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1171) from (by
          unfold nb078AlphaDummy1171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1246) 0)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1173 h) from (by
          unfold nb078AlphaDummy1173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1248 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1201) from (by
          unfold nb078AlphaDummy1201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1250) 0)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1202 h) from (by
          unfold nb078AlphaDummy1202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1251 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1175) from (by
          unfold nb078AlphaDummy1175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1247) 0)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1176 h) from (by
          unfold nb078AlphaDummy1176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1249 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb078AlphaDummy002)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy1130))).fv ∪
        ((Class.cv (nb078AlphaDummy1129))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1131 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0161 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)), ((nb078AlphaDummy1172),
        (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
        ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)), ((nb078AlphaDummy1175),
        (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy1129) ≠
        (nb078AlphaDummy1172) from (by
          unfold nb078AlphaDummy1172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1246) 1)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1174 h) from (by
          unfold nb078AlphaDummy1174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1248 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1171) from (by
          unfold nb078AlphaDummy1171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1246) 0)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1173 h) from (by
          unfold nb078AlphaDummy1173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1248 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1201) from (by
          unfold nb078AlphaDummy1201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1250) 0)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1202 h) from (by
          unfold nb078AlphaDummy1202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1251 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1175) from (by
          unfold nb078AlphaDummy1175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1247) 0)))) (show (nb078AlphaDummy1131 h) ≠
        (nb078AlphaDummy1176 h) from (by
          unfold nb078AlphaDummy1176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1249 h)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb078AlphaDummy002)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy1130))).fv ∪
        ((Class.cv (nb078AlphaDummy1129))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1131 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0161 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1203), (nb078AlphaDummy1204 h)), ((nb078AlphaDummy1172),
        (nb078AlphaDummy1174 h)), ((nb078AlphaDummy1171), (nb078AlphaDummy1173 h)),
        ((nb078AlphaDummy1201), (nb078AlphaDummy1202 h)), ((nb078AlphaDummy1175),
        (nb078AlphaDummy1176 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                              (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy851) from (by
                                  unfold nb078AlphaDummy851;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0880) 0)))))
                            (Ne.symm (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy852 h)
                                from (by
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
                              (Ne.symm (show
                                  (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy852 h) from (by
                                    unfold nb078AlphaDummy852;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0879 h)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb078SplitAlpha0162 x y h)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy848) ≠ (nb078AlphaDummy854) from (by
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
                  (nb078_support_mem_0912
                    h)
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
          unfold
            nb078AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy858 h) from (by
          unfold
            nb078AlphaDummy858;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0163 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
                  (nb078_support_mem_0912
                    h)
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
          unfold
            nb078AlphaDummy857;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0911)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy858 h) from (by
          unfold
            nb078AlphaDummy858;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0163 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb078SplitAlpha0164 x y h)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy847) ≠ (nb078AlphaDummy890) from (by
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
                  (nb078_support_mem_0950
                    h)
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
          unfold
            nb078AlphaDummy893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy894 h) from (by
          unfold
            nb078AlphaDummy894;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0165 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
                  (nb078_support_mem_0950
                    h)
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
          unfold
            nb078AlphaDummy893;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0949)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy894 h) from (by
          unfold
            nb078AlphaDummy894;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0165 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy1130), (nb078AlphaDummy1132 h)),
        ((nb078AlphaDummy1129), (nb078AlphaDummy1131 h)), ((nb078AlphaDummy1133),
        (nb078AlphaDummy1134 h)), ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)), ((nb078AlphaDummy1049),
        (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
                                          (mem_lt_freshVar (nb078_support_mem_0967 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy1130) from
                                    (by
                                      unfold nb078AlphaDummy1130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1266)
                                              1)))) (show h ≠ (nb078AlphaDummy1132 h) from
                                    (by
                                      unfold nb078AlphaDummy1132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1267 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy002) ≠ (nb078AlphaDummy1129) from
                                      (by
                                        unfold nb078AlphaDummy1129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1266)
                                                0)))) (show h ≠ (nb078AlphaDummy1131 h) from
                                      (by
                                        unfold nb078AlphaDummy1131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1267 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy002) ≠ (nb078AlphaDummy1133) from
                                        (by
                                          unfold nb078AlphaDummy1133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1264)
                                                  0))))
                                      (show h ≠ (nb078AlphaDummy1134 h) from (by
                                          unfold nb078AlphaDummy1134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1265 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy002) ≠
        (nb078AlphaDummy1051) from (by
          unfold nb078AlphaDummy1051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1260) 2)))) (show h ≠ (nb078AlphaDummy1054 h) from (by
          unfold nb078AlphaDummy1054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1262 h) 2)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy1050) from (by
          unfold nb078AlphaDummy1050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1260) 1)))) (show h ≠ (nb078AlphaDummy1053 h) from (by
          unfold nb078AlphaDummy1053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1262 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy1049) from (by
          unfold nb078AlphaDummy1049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1260) 0)))) (show h ≠ (nb078AlphaDummy1052 h) from (by
          unfold nb078AlphaDummy1052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1262 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy1055) from (by
          unfold nb078AlphaDummy1055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1261) 0)))) (show h ≠ (nb078AlphaDummy1056 h) from (by
          unfold nb078AlphaDummy1056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1263 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part184`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0167`. -/
@[expose]
noncomputable def nb078SplitAlpha0167 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
        ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
        ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
        ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
        ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1213))
          (Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1213)) (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCphi (Class.cv (nb078AlphaDummy1208)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1214 h))
          (Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1214 h))
            (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCphi (Class.cv (nb078AlphaDummy1210 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1208) from
                    (by
                      unfold nb078AlphaDummy1208;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
                  (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1210 h) from (by
                      unfold nb078AlphaDummy1210;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1207) from (by
                        unfold nb078AlphaDummy1207;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0))))
                    (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1209 h) from (by
                        unfold nb078AlphaDummy1209;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1270 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1213) from (by
                          unfold nb078AlphaDummy1213;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1272) 0))))
                      (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1214 h) from (by
                          unfold nb078AlphaDummy1214;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1273 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1211) from (by
                            unfold nb078AlphaDummy1211;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1269) 0))))
                        (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1212 h) from (by
                            unfold nb078AlphaDummy1212;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1271 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1051))).fv ∪
                      ((Class.cv (nb078AlphaDummy1050))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1215) from (by
                              unfold nb078AlphaDummy1215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                          (show (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1217 h) from (by
                              unfold nb078AlphaDummy1217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1216) from (by
                                unfold nb078AlphaDummy1216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 1))))
                            (show (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1218 h) from
                              (by
                                unfold nb078AlphaDummy1218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1208))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1222) from (by
          unfold nb078AlphaDummy1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1225 h) from (by
          unfold nb078AlphaDummy1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1221) from (by
          unfold nb078AlphaDummy1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1224 h) from (by
          unfold nb078AlphaDummy1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from (by
          unfold nb078AlphaDummy1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276) 0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1220 h) from (by
          unfold nb078AlphaDummy1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)), ((nb078AlphaDummy1207),
        (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
        ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)), ((nb078AlphaDummy1207),
        (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
        ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1217
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                      (by
                                        unfold nb078AlphaDummy1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078AlphaDummy1217 h) ≠
                                        (nb078AlphaDummy1220 h) from (by
                                        unfold nb078AlphaDummy1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                    ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                    ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                    ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                    ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                    ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
                                    ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from (by
                                      unfold nb078AlphaDummy1219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1276)
                                              0)))) (show (nb078AlphaDummy1217 h) ≠
                                      (nb078AlphaDummy1220 h) from (by
                                      unfold nb078AlphaDummy1220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1277 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                      (by
                                        unfold nb078AlphaDummy1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078AlphaDummy1217 h) ≠
                                        (nb078AlphaDummy1220 h) from (by
                                        unfold nb078AlphaDummy1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                    ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                    ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                    ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                    ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                    ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
                                    ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                    ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                    ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                    ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                    ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1208) from (by
                        unfold nb078AlphaDummy1208;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
                    (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1210 h) from (by
                        unfold nb078AlphaDummy1210;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1270 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1207) from (by
                          unfold nb078AlphaDummy1207;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1268) 0))))
                      (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1209 h) from (by
                          unfold nb078AlphaDummy1209;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1270 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1213) from (by
                            unfold nb078AlphaDummy1213;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1272) 0))))
                        (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1214 h) from (by
                            unfold nb078AlphaDummy1214;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1273 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1211) from (by
                              unfold nb078AlphaDummy1211;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1269) 0))))
                          (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1212 h) from (by
                              unfold nb078AlphaDummy1212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1271 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy1051))).fv ∪
                        ((Class.cv (nb078AlphaDummy1050))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy1053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1215) from (by
                                unfold nb078AlphaDummy1215;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1274) 0))))
                            (show (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1217 h) from
                              (by
                                unfold nb078AlphaDummy1217;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1275 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1208) ≠ (nb078AlphaDummy1216) from (by
                                  unfold nb078AlphaDummy1216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1274) 1)))) (show
                                (nb078AlphaDummy1210 h) ≠ (nb078AlphaDummy1218 h) from (by
                                  unfold nb078AlphaDummy1218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1275 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy1208))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy1210 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1222) from (by
          unfold nb078AlphaDummy1222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 1)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1225 h) from (by
          unfold nb078AlphaDummy1225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1221) from (by
          unfold nb078AlphaDummy1221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1278) 0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1224 h) from (by
          unfold nb078AlphaDummy1224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1279 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1215) ≠
        (nb078AlphaDummy1219) from (by
          unfold nb078AlphaDummy1219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1276)
                  0)))) (show (nb078AlphaDummy1217 h) ≠ (nb078AlphaDummy1220 h) from (by
          unfold nb078AlphaDummy1220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1277 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)), ((nb078AlphaDummy1207),
        (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
        ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1282)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1283
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1280)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1281
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1229) from (by
          unfold
            nb078AlphaDummy1229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1286)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1230 h) from (by
          unfold
            nb078AlphaDummy1230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1287
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1227) from (by
          unfold
            nb078AlphaDummy1227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1284)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1228 h) from (by
          unfold
            nb078AlphaDummy1228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1285
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1223), (nb078AlphaDummy1226 h)), ((nb078AlphaDummy1222),
        (nb078AlphaDummy1225 h)), ((nb078AlphaDummy1221), (nb078AlphaDummy1224 h)),
        ((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)), ((nb078AlphaDummy1215),
        (nb078AlphaDummy1217 h)), ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
        ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)), ((nb078AlphaDummy1207),
        (nb078AlphaDummy1209 h)), ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
        ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)), ((nb078AlphaDummy1051),
        (nb078AlphaDummy1054 h)), ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
        ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)), ((nb078AlphaDummy1055),
        (nb078AlphaDummy1056 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1215))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1217
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1222) ≠ (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1233) from (by
          unfold
            nb078AlphaDummy1233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1290)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1234 h) from (by
          unfold
            nb078AlphaDummy1234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1291
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1222) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1288)
                  0)))) (show (nb078AlphaDummy1225 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1289
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1223) ≠ (nb078AlphaDummy1235) from (by
          unfold
            nb078AlphaDummy1235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1294)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1236 h) from (by
          unfold
            nb078AlphaDummy1236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1295
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1223) ≠
        (nb078AlphaDummy1231) from (by
          unfold
            nb078AlphaDummy1231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1292)
                  0)))) (show (nb078AlphaDummy1226 h) ≠ (nb078AlphaDummy1232 h) from (by
          unfold
            nb078AlphaDummy1232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1293
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                        (by
                                          unfold nb078AlphaDummy1219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1276)
                                                  0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1220 h) from (by
                                          unfold nb078AlphaDummy1220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1277 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                      ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                      ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                      ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                      ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                      ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
                                      ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                      (by
                                        unfold nb078AlphaDummy1219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1276)
                                                0)))) (show (nb078AlphaDummy1217 h) ≠
                                        (nb078AlphaDummy1220 h) from (by
                                        unfold nb078AlphaDummy1220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1277 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1215) ≠ (nb078AlphaDummy1219) from
                                        (by
                                          unfold nb078AlphaDummy1219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1276)
                                                  0)))) (show (nb078AlphaDummy1217 h) ≠
        (nb078AlphaDummy1220 h) from (by
                                          unfold nb078AlphaDummy1220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1277 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1219), (nb078AlphaDummy1220 h)),
                                      ((nb078AlphaDummy1215), (nb078AlphaDummy1217 h)),
                                      ((nb078AlphaDummy1216), (nb078AlphaDummy1218 h)),
                                      ((nb078AlphaDummy1208), (nb078AlphaDummy1210 h)),
                                      ((nb078AlphaDummy1207), (nb078AlphaDummy1209 h)),
                                      ((nb078AlphaDummy1213), (nb078AlphaDummy1214 h)),
                                      ((nb078AlphaDummy1211), (nb078AlphaDummy1212 h)),
                                      ((nb078AlphaDummy1051), (nb078AlphaDummy1054 h)),
                                      ((nb078AlphaDummy1050), (nb078AlphaDummy1053 h)),
                                      ((nb078AlphaDummy1049), (nb078AlphaDummy1052 h)),
                                      ((nb078AlphaDummy1055), (nb078AlphaDummy1056 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
