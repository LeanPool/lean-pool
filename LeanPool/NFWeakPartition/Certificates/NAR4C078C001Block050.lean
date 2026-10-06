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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0128`. -/
@[expose]
noncomputable def nb078SplitAlpha0128 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
        ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy921))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy890))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy921)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy922 h))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy892 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy922 h))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy923) from (by
                                  unfold nb078AlphaDummy923;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                              (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy924 h) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0954) 0)))) (show
                                  (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy922 h) from (by
                                    unfold nb078AlphaDummy922;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0955 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy923), (nb078AlphaDummy924 h)), ((nb078AlphaDummy921),
        (nb078AlphaDummy922 h)), ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)), ((nb078AlphaDummy919),
        (nb078AlphaDummy920 h)), ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078AlphaDummy923), (nb078AlphaDummy924 h)), ((nb078AlphaDummy921),
        (nb078AlphaDummy922 h)), ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)), ((nb078AlphaDummy919),
        (nb078AlphaDummy920 h)), ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy899
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915) from (by
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
                                    ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                                    ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
                                    ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
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
                                    ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                                    ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
                                    ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078AlphaDummy890) ≠ (nb078AlphaDummy923) from (by
                                  unfold nb078AlphaDummy923;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0956) 0))))
                              (show (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy924 h) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0954) 0)))) (show
                                  (nb078AlphaDummy892 h) ≠ (nb078AlphaDummy922 h) from (by
                                    unfold nb078AlphaDummy922;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0955 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy923), (nb078AlphaDummy924 h)), ((nb078AlphaDummy921),
        (nb078AlphaDummy922 h)), ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)), ((nb078AlphaDummy919),
        (nb078AlphaDummy920 h)), ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
        ((nb078AlphaDummy923), (nb078AlphaDummy924 h)), ((nb078AlphaDummy921),
        (nb078AlphaDummy922 h)), ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
        ((nb078AlphaDummy889), (nb078AlphaDummy891 h)), ((nb078AlphaDummy919),
        (nb078AlphaDummy920 h)), ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)), ((nb078AlphaDummy847),
        (nb078AlphaDummy849 h)), ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy962), (nb078AlphaDummy964 h)), ((nb078AlphaDummy961),
        (nb078AlphaDummy963 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy897))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy899
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy904) ≠ (nb078AlphaDummy915) from (by
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
                                    ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                                    ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
                                    ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
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
                                    ((nb078AlphaDummy923), (nb078AlphaDummy924 h)),
                                    ((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
                                    ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy921), (nb078AlphaDummy922 h)),
            ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
            ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
            ((nb078AlphaDummy919), (nb078AlphaDummy920 h)),
            ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
            ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
            ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
            ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
            ((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
            ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
            ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0129`. -/
@[expose]
noncomputable def nb078SplitAlpha0129 (x : Var) (y : Var) (h : Var) (dv_h_x : h ≠ x)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (synWfun (Class.cv (nb078AlphaDummy002))) (Wff.neg
          (Wff.classEq (synCdm (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy003)))))
      (Wff.imp (synWfun (Class.cv h))
        (Wff.neg (Wff.classEq (synCdm (Class.cv h)) (Class.cv x)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0112 x y h))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                          ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                          ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                          ((nb078AlphaDummy003), x)]
                        (synCid) (nb078WppRefl0372 x y h)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0112 x y h))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb078AlphaDummy765), (nb078AlphaDummy766 h)),
                          ((nb078AlphaDummy763), (nb078AlphaDummy764 h)),
                          ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                          ((nb078AlphaDummy003), x)]
                        (synCid) (nb078WppRefl0372 x y h)))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy773) from (by
                          unfold nb078AlphaDummy773;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0800) 0))))) (Ne.symm
                      (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy774 h) from (by
                          unfold nb078AlphaDummy774;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0801 h) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb078AlphaDummy767) ≠ (nb078AlphaDummy773) from (by
                            unfold nb078AlphaDummy773;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0798) 0))))) (Ne.symm
                        (show (nb078AlphaDummy770 h) ≠ (nb078AlphaDummy774 h) from (by
                            unfold nb078AlphaDummy774;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0799 h) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0113 x y h)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb078SplitAlpha0114 x y h)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb078SplitAlpha0114 x y h))))))))))))) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0115 x y h)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy769) ≠ (nb078AlphaDummy812) from (by
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
                  (nb078_support_mem_0870 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy811)
        from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868)
                  0)))) (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy841)
        from (by
          unfold nb078AlphaDummy841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872)
                  0)))) (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy842 h) from (by
          unfold nb078AlphaDummy842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy815)
        from (by
          unfold nb078AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869)
                  0)))) (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy816 h) from (by
          unfold nb078AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy767))).fv ∪
        ((Class.cv (nb078AlphaDummy769))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0116 x y h)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy812) from (by
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
                  (nb078_support_mem_0870 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy811)
        from (by
          unfold nb078AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0868)
                  0)))) (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy813 h) from (by
          unfold nb078AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0870 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy841)
        from (by
          unfold nb078AlphaDummy841;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0872)
                  0)))) (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy842 h) from (by
          unfold nb078AlphaDummy842;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0873 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy815)
        from (by
          unfold nb078AlphaDummy815;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0869)
                  0)))) (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy816 h) from (by
          unfold nb078AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0871
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy767))).fv ∪
        ((Class.cv (nb078AlphaDummy769))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy770 h))).fv ∪ ((Class.cv (nb078AlphaDummy772 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0116 x y h))))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb078AlphaDummy848) ≠ (nb078AlphaDummy851) from (by
                                        unfold nb078AlphaDummy851;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0880)
                                                0))))) (Ne.symm (show
                                      (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy852 h) from
                                      (by
                                        unfold nb078AlphaDummy852;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0881 h)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb078AlphaDummy847) ≠ (nb078AlphaDummy851) from
                                        (by
                                          unfold nb078AlphaDummy851;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0878)
                                                  0))))) (Ne.symm (show
                                        (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy852 h)
                                        from (by
                                          unfold nb078AlphaDummy852;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0879 h) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0117 x y h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy854) from (by
          unfold
            nb078AlphaDummy854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy856 h) from (by
          unfold
            nb078AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy853)
        from (by
          unfold
            nb078AlphaDummy853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold
            nb078AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy883)
        from (by
          unfold
            nb078AlphaDummy883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy884 h) from (by
          unfold
            nb078AlphaDummy884;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0118 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy848) ≠
        (nb078AlphaDummy854) from (by
          unfold
            nb078AlphaDummy854;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  1)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy856 h) from (by
          unfold
            nb078AlphaDummy856;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy853)
        from (by
          unfold
            nb078AlphaDummy853;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0910)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold
            nb078AlphaDummy855;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0912
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy883)
        from (by
          unfold
            nb078AlphaDummy883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy884 h) from (by
          unfold
            nb078AlphaDummy884;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0118 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy885), (nb078AlphaDummy886 h)), ((nb078AlphaDummy854),
        (nb078AlphaDummy856 h)), ((nb078AlphaDummy853), (nb078AlphaDummy855 h)),
        ((nb078AlphaDummy883), (nb078AlphaDummy884 h)), ((nb078AlphaDummy857),
        (nb078AlphaDummy858 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0119 x y h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy890) from (by
          unfold
            nb078AlphaDummy890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy892 h) from (by
          unfold
            nb078AlphaDummy892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy889)
        from (by
          unfold
            nb078AlphaDummy889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold
            nb078AlphaDummy891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy919)
        from (by
          unfold
            nb078AlphaDummy919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy920 h) from (by
          unfold
            nb078AlphaDummy920;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0120 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy847) ≠
        (nb078AlphaDummy890) from (by
          unfold
            nb078AlphaDummy890;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  1)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy892 h) from (by
          unfold
            nb078AlphaDummy892;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy889)
        from (by
          unfold
            nb078AlphaDummy889;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0948)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold
            nb078AlphaDummy891;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0950
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy919)
        from (by
          unfold
            nb078AlphaDummy919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy920 h) from (by
          unfold
            nb078AlphaDummy920;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0120 x y h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy921), (nb078AlphaDummy922 h)), ((nb078AlphaDummy890),
        (nb078AlphaDummy892 h)), ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
        ((nb078AlphaDummy919), (nb078AlphaDummy920 h)), ((nb078AlphaDummy893),
        (nb078AlphaDummy894 h)), ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)), ((nb078AlphaDummy851),
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy848) from
                                    (by
                                      unfold nb078AlphaDummy848;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0968)
                                              1)))) (show h ≠ (nb078AlphaDummy850 h) from (by
                                      unfold nb078AlphaDummy850;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0969 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy002) ≠ (nb078AlphaDummy847) from (by
                                        unfold nb078AlphaDummy847;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0968)
                                                0)))) (show h ≠ (nb078AlphaDummy849 h) from
                                      (by
                                        unfold nb078AlphaDummy849;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0969 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy002) ≠ (nb078AlphaDummy851) from
                                        (by
                                          unfold nb078AlphaDummy851;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0966)
                                                  0)))) (show h ≠ (nb078AlphaDummy852 h) from
                                        (by
                                          unfold nb078AlphaDummy852;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0967 h) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy002) ≠
        (nb078AlphaDummy769) from (by
          unfold nb078AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0962) 2)))) (show h ≠ (nb078AlphaDummy772 h) from (by
          unfold nb078AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0964 h) 2)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy768) from (by
          unfold nb078AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0962) 1)))) (show h ≠ (nb078AlphaDummy771 h) from (by
          unfold nb078AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0964 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy767) from (by
          unfold nb078AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0962) 0)))) (show h ≠ (nb078AlphaDummy770 h) from (by
          unfold nb078AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0964 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy002) ≠ (nb078AlphaDummy773) from (by
          unfold nb078AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0963) 0)))) (show h ≠ (nb078AlphaDummy774 h) from (by
          unfold nb078AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0965 h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0121 x y h)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy768) ≠ (nb078AlphaDummy926) from (by
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
                  (nb078_support_mem_1000 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy925)
        from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998)
                  0)))) (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy955)
        from (by
          unfold nb078AlphaDummy955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002)
                  0)))) (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy956 h) from (by
          unfold nb078AlphaDummy956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy929)
        from (by
          unfold nb078AlphaDummy929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999)
                  0)))) (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy930 h) from (by
          unfold nb078AlphaDummy930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy002))).fv ∪ ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv)
        (by decide)) (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy769))).fv ∪
        ((Class.cv (nb078AlphaDummy768))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0122 x y h)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy926) from (by
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
                  (nb078_support_mem_1000 h)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy925)
        from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0998)
                  0)))) (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1000 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy955)
        from (by
          unfold nb078AlphaDummy955;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1002)
                  0)))) (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy956 h) from (by
          unfold nb078AlphaDummy956;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1003 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy929)
        from (by
          unfold nb078AlphaDummy929;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0999)
                  0)))) (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy930 h) from (by
          unfold nb078AlphaDummy930;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1001
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy002))).fv ∪ ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv)
        (by decide)) (freshVar_injective (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy769))).fv ∪
        ((Class.cv (nb078AlphaDummy768))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0122 x y h))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.there
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
                                  (mem_lt_freshVar (nb078_support_mem_0964 h) 2))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy768) from (by
                              unfold nb078AlphaDummy768;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0962) 1))))
                          (show h ≠ (nb078AlphaDummy771 h) from (by
                              unfold nb078AlphaDummy771;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0964 h) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy767) from (by
                                unfold nb078AlphaDummy767;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0962) 0))))
                            (show h ≠ (nb078AlphaDummy770 h) from (by
                                unfold nb078AlphaDummy770;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0964 h) 0))))
                            (TAlphaVar.there
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
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy962), (nb078AlphaDummy964 h)),
                    ((nb078AlphaDummy961), (nb078AlphaDummy963 h)),
                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0124 x y h))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                                (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy851) from (by
                                    unfold nb078AlphaDummy851;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0880) 0)))))
                              (Ne.symm (show
                                  (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy852 h) from (by
                                    unfold nb078AlphaDummy852;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0881 h)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy851) from
                                    (by
                                      unfold nb078AlphaDummy851;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0878)
                                              0))))) (Ne.symm (show
                                    (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy852 h) from
                                    (by
                                      unfold nb078AlphaDummy852;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0879 h)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078SplitAlpha0125 x y h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0912
                    h)
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
          unfold
            nb078AlphaDummy883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy884 h) from (by
          unfold
            nb078AlphaDummy884;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0126 x y h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0912
                    h)
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
          unfold
            nb078AlphaDummy883;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0914)
                  0)))) (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy884 h) from (by
          unfold
            nb078AlphaDummy884;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0126 x y h))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078SplitAlpha0127 x y h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0950
                    h)
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
          unfold
            nb078AlphaDummy919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy920 h) from (by
          unfold
            nb078AlphaDummy920;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0128 x y h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0950
                    h)
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
          unfold
            nb078AlphaDummy919;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0952)
                  0)))) (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy920 h) from (by
          unfold
            nb078AlphaDummy920;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0128 x y h)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
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
                                          (mem_lt_freshVar (nb078_support_mem_0969 h)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy851) from
                                    (by
                                      unfold nb078AlphaDummy851;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0966)
                                              0)))) (show h ≠ (nb078AlphaDummy852 h) from (by
                                      unfold nb078AlphaDummy852;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0967 h)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy002) ≠ (nb078AlphaDummy962) from (by
                                        unfold nb078AlphaDummy962;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1046)
                                                1)))) (show h ≠ (nb078AlphaDummy964 h) from
                                      (by
                                        unfold nb078AlphaDummy964;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1047 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy002) ≠ (nb078AlphaDummy961) from
                                        (by
                                          unfold nb078AlphaDummy961;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1046)
                                                  0)))) (show h ≠ (nb078AlphaDummy963 h) from
                                        (by
                                          unfold nb078AlphaDummy963;
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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0130`. -/
@[expose]
noncomputable def nb078SplitAlpha0130 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
        ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
        ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
        ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1015))
          (Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1015)) (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCphi (Class.cv (nb078AlphaDummy1010)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy1016 h))
          (Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy1016 h))
            (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCphi (Class.cv (nb078AlphaDummy1012 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1010) from
                    (by
                      unfold nb078AlphaDummy1010;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                  (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1012 h) from (by
                      unfold nb078AlphaDummy1012;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1009) from (by
                        unfold nb078AlphaDummy1009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                    (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1011 h) from (by
                        unfold nb078AlphaDummy1011;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1050 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1015) from (by
                          unfold nb078AlphaDummy1015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1052) 0))))
                      (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1016 h) from (by
                          unfold nb078AlphaDummy1016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1013) from (by
                            unfold nb078AlphaDummy1013;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1049) 0))))
                        (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1014 h) from (by
                            unfold nb078AlphaDummy1014;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1051 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1006))).fv ∪
                      ((Class.cv (nb078AlphaDummy1005))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy1007 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from (by
                              unfold nb078AlphaDummy1017;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                          (show (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1019 h) from (by
                              unfold nb078AlphaDummy1019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from (by
                                unfold nb078AlphaDummy1018;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 1))))
                            (show (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1020 h) from
                              (by
                                unfold nb078AlphaDummy1020;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1010))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy1012 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)), ((nb078AlphaDummy1001),
        (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)), ((nb078AlphaDummy1001),
        (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                      (by
                                        unfold nb078AlphaDummy1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078AlphaDummy1019 h) ≠
                                        (nb078AlphaDummy1022 h) from (by
                                        unfold nb078AlphaDummy1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                    ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                    ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                    ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                    ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                    ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
                                    ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                    ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                    ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                    ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                    ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from (by
                                      unfold nb078AlphaDummy1021;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1056)
                                              0)))) (show (nb078AlphaDummy1019 h) ≠
                                      (nb078AlphaDummy1022 h) from (by
                                      unfold nb078AlphaDummy1022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_1057 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                      (by
                                        unfold nb078AlphaDummy1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078AlphaDummy1019 h) ≠
                                        (nb078AlphaDummy1022 h) from (by
                                        unfold nb078AlphaDummy1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                    ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                    ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                    ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                    ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                    ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
                                    ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                    ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                    ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                    ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                    ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1010) from (by
                        unfold nb078AlphaDummy1010;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
                    (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1012 h) from (by
                        unfold nb078AlphaDummy1012;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_1050 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1009) from (by
                          unfold nb078AlphaDummy1009;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1048) 0))))
                      (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1011 h) from (by
                          unfold nb078AlphaDummy1011;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1015) from (by
                            unfold nb078AlphaDummy1015;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1052) 0))))
                        (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1016 h) from (by
                            unfold nb078AlphaDummy1016;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_1053 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1013) from (by
                              unfold nb078AlphaDummy1013;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1049) 0))))
                          (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1014 h) from (by
                              unfold nb078AlphaDummy1014;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_1051 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy1006))).fv ∪
                        ((Class.cv (nb078AlphaDummy1005))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy1007 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1017) from (by
                                unfold nb078AlphaDummy1017;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1054) 0))))
                            (show (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1019 h) from
                              (by
                                unfold nb078AlphaDummy1019;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_1055 h) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy1010) ≠ (nb078AlphaDummy1018) from (by
                                  unfold nb078AlphaDummy1018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1054) 1)))) (show
                                (nb078AlphaDummy1012 h) ≠ (nb078AlphaDummy1020 h) from (by
                                  unfold nb078AlphaDummy1020;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_1055 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy1010))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy1012 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1024) from (by
          unfold nb078AlphaDummy1024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 1)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1027 h) from (by
          unfold nb078AlphaDummy1027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1023) from (by
          unfold nb078AlphaDummy1023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1058) 0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1026 h) from (by
          unfold nb078AlphaDummy1026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1059 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1017) ≠
        (nb078AlphaDummy1021) from (by
          unfold nb078AlphaDummy1021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1056)
                  0)))) (show (nb078AlphaDummy1019 h) ≠ (nb078AlphaDummy1022 h) from (by
          unfold nb078AlphaDummy1022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1057 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)), ((nb078AlphaDummy1001),
        (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1062)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1063
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1060)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1061
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1031) from (by
          unfold
            nb078AlphaDummy1031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1066)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1032 h) from (by
          unfold
            nb078AlphaDummy1032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1067
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1029) from (by
          unfold
            nb078AlphaDummy1029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1064)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1030 h) from (by
          unfold
            nb078AlphaDummy1030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1065
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy1025), (nb078AlphaDummy1028 h)), ((nb078AlphaDummy1024),
        (nb078AlphaDummy1027 h)), ((nb078AlphaDummy1023), (nb078AlphaDummy1026 h)),
        ((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)), ((nb078AlphaDummy1017),
        (nb078AlphaDummy1019 h)), ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
        ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)), ((nb078AlphaDummy1009),
        (nb078AlphaDummy1011 h)), ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
        ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)), ((nb078AlphaDummy1006),
        (nb078AlphaDummy1008 h)), ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
        ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)), ((nb078AlphaDummy1001),
        (nb078AlphaDummy1002 y h)), ((nb078AlphaDummy002), h),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy1017))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy1019
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1024) ≠ (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1035) from (by
          unfold
            nb078AlphaDummy1035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1070)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1036 h) from (by
          unfold
            nb078AlphaDummy1036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1071
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1024) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1068)
                  0)))) (show (nb078AlphaDummy1027 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1069
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy1025) ≠ (nb078AlphaDummy1037) from (by
          unfold
            nb078AlphaDummy1037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1074)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1038 h) from (by
          unfold
            nb078AlphaDummy1038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1075
                    h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy1025) ≠
        (nb078AlphaDummy1033) from (by
          unfold
            nb078AlphaDummy1033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1072)
                  0)))) (show (nb078AlphaDummy1028 h) ≠ (nb078AlphaDummy1034 h) from (by
          unfold
            nb078AlphaDummy1034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_1073
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                        (by
                                          unfold nb078AlphaDummy1021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1056)
                                                  0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
                                          unfold nb078AlphaDummy1022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1057 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                      ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                      ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                      ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                      ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                      ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
                                      ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                      ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                      ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                      ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                      ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                      (by
                                        unfold nb078AlphaDummy1021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1056)
                                                0)))) (show (nb078AlphaDummy1019 h) ≠
                                        (nb078AlphaDummy1022 h) from (by
                                        unfold nb078AlphaDummy1022;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_1057 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1021) from
                                        (by
                                          unfold nb078AlphaDummy1021;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_1056)
                                                  0)))) (show (nb078AlphaDummy1019 h) ≠
        (nb078AlphaDummy1022 h) from (by
                                          unfold nb078AlphaDummy1022;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_1057 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy1021), (nb078AlphaDummy1022 h)),
                                      ((nb078AlphaDummy1017), (nb078AlphaDummy1019 h)),
                                      ((nb078AlphaDummy1018), (nb078AlphaDummy1020 h)),
                                      ((nb078AlphaDummy1010), (nb078AlphaDummy1012 h)),
                                      ((nb078AlphaDummy1009), (nb078AlphaDummy1011 h)),
                                      ((nb078AlphaDummy1015), (nb078AlphaDummy1016 h)),
                                      ((nb078AlphaDummy1013), (nb078AlphaDummy1014 h)),
                                      ((nb078AlphaDummy1006), (nb078AlphaDummy1008 h)),
                                      ((nb078AlphaDummy1005), (nb078AlphaDummy1007 h)),
                                      ((nb078AlphaDummy1003), (nb078AlphaDummy1004 y h)),
                                      ((nb078AlphaDummy1001), (nb078AlphaDummy1002 y h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
