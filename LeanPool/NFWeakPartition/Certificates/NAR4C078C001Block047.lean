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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0119`. -/
@[expose]
noncomputable def nb078SplitAlpha0119 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
        ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
        ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
                                    ((nb078AlphaDummy890), (nb078AlphaDummy892 h)),
                                    ((nb078AlphaDummy889), (nb078AlphaDummy891 h)),
                                    ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
                                    ((nb078AlphaDummy893), (nb078AlphaDummy894 h)),
                                    ((nb078AlphaDummy848), (nb078AlphaDummy850 h)),
                                    ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
                                    ((nb078AlphaDummy851), (nb078AlphaDummy852 h)),
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy890), (nb078AlphaDummy892 h)), ((nb078AlphaDummy889),
        (nb078AlphaDummy891 h)), ((nb078AlphaDummy895), (nb078AlphaDummy896 h)),
        ((nb078AlphaDummy893), (nb078AlphaDummy894 h)), ((nb078AlphaDummy848),
        (nb078AlphaDummy850 h)), ((nb078AlphaDummy847), (nb078AlphaDummy849 h)),
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0120`. -/
@[expose]
noncomputable def nb078SplitAlpha0120 (x : Var) (y : Var) (h : Var) :
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
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                                        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
        (nb078AlphaDummy852 h)), ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)), ((nb078AlphaDummy767),
        (nb078AlphaDummy770 h)), ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                            ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                            ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                            ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                            ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                            ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                            ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                            ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                            ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
        ((nb078AlphaDummy851), (nb078AlphaDummy852 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)), ((nb078AlphaDummy768),
        (nb078AlphaDummy771 h)), ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h),
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
                              ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                              ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                              ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                              ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
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
                              ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                              ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                              ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                              ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                              ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0121`. -/
@[expose]
noncomputable def nb078SplitAlpha0121 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
        ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
        ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
        ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
        ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
        ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy931))
          (Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy931)) (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCphi (Class.cv (nb078AlphaDummy926)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy932 h))
          (Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy932 h))
            (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCphi (Class.cv (nb078AlphaDummy928 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy926) from
                    (by
                      unfold nb078AlphaDummy926;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
                  (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy928 h) from (by
                      unfold nb078AlphaDummy928;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy925) from
                      (by
                        unfold nb078AlphaDummy925;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))))
                    (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy927 h) from (by
                        unfold nb078AlphaDummy927;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0972 h) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy931) from (by
                          unfold nb078AlphaDummy931;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0974) 0))))
                      (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy932 h) from (by
                          unfold nb078AlphaDummy932;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0975 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy929) from (by
                            unfold nb078AlphaDummy929;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0971) 0))))
                        (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy930 h) from (by
                            unfold nb078AlphaDummy930;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0973 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy769))).fv ∪
                      ((Class.cv (nb078AlphaDummy768))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy772 h))).fv ∪
                      ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy926))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy928 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy940) from (by
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
                  (nb078_support_mem_0979 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy941), (nb078AlphaDummy944 h)), ((nb078AlphaDummy940),
        (nb078AlphaDummy943 h)), ((nb078AlphaDummy939), (nb078AlphaDummy942 h)),
        ((nb078AlphaDummy937), (nb078AlphaDummy938 h)), ((nb078AlphaDummy933),
        (nb078AlphaDummy935 h)), ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
        ((nb078AlphaDummy926), (nb078AlphaDummy928 h)), ((nb078AlphaDummy925),
        (nb078AlphaDummy927 h)), ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
        ((nb078AlphaDummy929), (nb078AlphaDummy930 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy926), (nb078AlphaDummy928 h)), ((nb078AlphaDummy925),
        (nb078AlphaDummy927 h)), ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
        ((nb078AlphaDummy929), (nb078AlphaDummy930 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy935
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
                                        unfold nb078AlphaDummy937;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0978)
                                                0)))) (show (nb078AlphaDummy935 h) ≠
                                        (nb078AlphaDummy938 h) from (by
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
                                    ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                    ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                    ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
                                    ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
                                        unfold nb078AlphaDummy937;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0978)
                                                0)))) (show (nb078AlphaDummy935 h) ≠
                                        (nb078AlphaDummy938 h) from (by
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
                                    ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                    ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                    ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
                                    ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
                                    ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                    ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                    ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                    ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                    ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy926) from
                      (by
                        unfold nb078AlphaDummy926;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
                    (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy928 h) from (by
                        unfold nb078AlphaDummy928;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0972 h) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy925) from (by
                          unfold nb078AlphaDummy925;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0970) 0))))
                      (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy927 h) from (by
                          unfold nb078AlphaDummy927;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0972 h) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy931) from (by
                            unfold nb078AlphaDummy931;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0974) 0))))
                        (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy932 h) from (by
                            unfold nb078AlphaDummy932;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0975 h) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy929) from (by
                              unfold nb078AlphaDummy929;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0971) 0))))
                          (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy930 h) from (by
                              unfold nb078AlphaDummy930;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0973 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy769))).fv ∪
                        ((Class.cv (nb078AlphaDummy768))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy772 h))).fv ∪
                        ((Class.cv (nb078AlphaDummy771 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
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
                              (show (nb078AlphaDummy928 h) ≠ (nb078AlphaDummy936 h) from
                                (by
                                  unfold nb078AlphaDummy936;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0977 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy926))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy928 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy933) ≠ (nb078AlphaDummy940) from (by
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
                  (nb078_support_mem_0981 h)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy933) ≠ (nb078AlphaDummy937)
        from (by
          unfold nb078AlphaDummy937;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0978)
                  0)))) (show (nb078AlphaDummy935 h) ≠ (nb078AlphaDummy938 h) from (by
          unfold nb078AlphaDummy938;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0979 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy941), (nb078AlphaDummy944 h)), ((nb078AlphaDummy940),
        (nb078AlphaDummy943 h)), ((nb078AlphaDummy939), (nb078AlphaDummy942 h)),
        ((nb078AlphaDummy937), (nb078AlphaDummy938 h)), ((nb078AlphaDummy933),
        (nb078AlphaDummy935 h)), ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
        ((nb078AlphaDummy926), (nb078AlphaDummy928 h)), ((nb078AlphaDummy925),
        (nb078AlphaDummy927 h)), ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
        ((nb078AlphaDummy929), (nb078AlphaDummy930 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy926), (nb078AlphaDummy928 h)), ((nb078AlphaDummy925),
        (nb078AlphaDummy927 h)), ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
        ((nb078AlphaDummy929), (nb078AlphaDummy930 h)), ((nb078AlphaDummy769),
        (nb078AlphaDummy772 h)), ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
        ((nb078AlphaDummy767), (nb078AlphaDummy770 h)), ((nb078AlphaDummy773),
        (nb078AlphaDummy774 h)), ((nb078AlphaDummy002), h), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy933))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy935
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                        (by
                                          unfold nb078AlphaDummy937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
                                          unfold nb078AlphaDummy938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy937), (nb078AlphaDummy938 h)),
                                      ((nb078AlphaDummy933), (nb078AlphaDummy935 h)),
                                      ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
                                      ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                      ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                      ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
                                      ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from (by
                                        unfold nb078AlphaDummy937;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0978)
                                                0)))) (show (nb078AlphaDummy935 h) ≠
                                        (nb078AlphaDummy938 h) from (by
                                        unfold nb078AlphaDummy938;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0979 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy933) ≠ (nb078AlphaDummy937) from
                                        (by
                                          unfold nb078AlphaDummy937;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0978)
                                                  0)))) (show (nb078AlphaDummy935 h) ≠
        (nb078AlphaDummy938 h) from (by
                                          unfold nb078AlphaDummy938;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0979 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy937), (nb078AlphaDummy938 h)),
                                      ((nb078AlphaDummy933), (nb078AlphaDummy935 h)),
                                      ((nb078AlphaDummy934), (nb078AlphaDummy936 h)),
                                      ((nb078AlphaDummy926), (nb078AlphaDummy928 h)),
                                      ((nb078AlphaDummy925), (nb078AlphaDummy927 h)),
                                      ((nb078AlphaDummy931), (nb078AlphaDummy932 h)),
                                      ((nb078AlphaDummy929), (nb078AlphaDummy930 h)),
                                      ((nb078AlphaDummy769), (nb078AlphaDummy772 h)),
                                      ((nb078AlphaDummy768), (nb078AlphaDummy771 h)),
                                      ((nb078AlphaDummy767), (nb078AlphaDummy770 h)),
                                      ((nb078AlphaDummy773), (nb078AlphaDummy774 h)),
                                      ((nb078AlphaDummy002), h),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
