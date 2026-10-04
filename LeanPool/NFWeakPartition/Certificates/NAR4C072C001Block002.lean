/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C072C001Part007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C072C001Part009`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0001`. -/
@[expose]
noncomputable def nb072SplitAlpha0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072AlphaDummy060 A B R S_cls H), (nb072AlphaDummy061 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy060 A B R S_cls H))
          (Class.cab (nb072AlphaDummy054 A B R S_cls H)
            (synWrex (nb072AlphaDummy055 A B R S_cls H)
              (Class.cv (nb072AlphaDummy000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy060 A B R S_cls H))
            (Class.cab (nb072AlphaDummy054 A B R S_cls H)
              (synWrex (nb072AlphaDummy055 A B R S_cls H)
                (Class.cv (nb072AlphaDummy000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072AlphaDummy054 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy061 x H))
          (Class.cab (nb072AlphaDummy056 x H)
            (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                (synCphi (Class.cv (nb072AlphaDummy057 x H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy061 x H))
            (Class.cab (nb072AlphaDummy056 x H)
              (synWrex (nb072AlphaDummy057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072AlphaDummy056 x H))
                  (synCphi (Class.cv (nb072AlphaDummy057 x H))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                      (nb072AlphaDummy055 A B R S_cls H) from (by
                      unfold nb072AlphaDummy055;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))))
                  (show x ≠ (nb072AlphaDummy057 x H) from (by
                      unfold nb072AlphaDummy057;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0052 x H) 1)))) (TAlphaVar.there
                    (show (nb072AlphaDummy000 A B R S_cls H) ≠
                        (nb072AlphaDummy054 A B R S_cls H) from (by
                        unfold nb072AlphaDummy054;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H)
                                0)))) (show x ≠ (nb072AlphaDummy056 x H) from (by
                        unfold nb072AlphaDummy056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
                    (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                          (nb072AlphaDummy060 A B R S_cls H) from (by
                          unfold nb072AlphaDummy060;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0054 A B R S_cls H)
                                  0)))) (show x ≠ (nb072AlphaDummy061 x H) from (by
                          unfold nb072AlphaDummy061;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0055 x H) 0))))
                      (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                            (nb072AlphaDummy058 A B R S_cls H) from (by
                            unfold nb072AlphaDummy058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0051 A B R S_cls H)
                                    0)))) (show x ≠ (nb072AlphaDummy059 x H) from (by
                            unfold nb072AlphaDummy059;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0053 x H) 0))))
                        (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                              (nb072AlphaDummy046 A B R S_cls H) from (by
                              unfold nb072AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0044 A B R S_cls H) 0))))
                          (show x ≠ (nb072AlphaDummy047 x H) from (by
                              unfold nb072AlphaDummy047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0047 x H) 0))))
                          (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                                (nb072AlphaDummy048 A B R S_cls H) from (by
                                unfold nb072AlphaDummy048;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0045 A B R S_cls H) 0))))
                            (show x ≠ (nb072AlphaDummy049 x H) from (by
                                unfold nb072AlphaDummy049;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0048 x H) 0))))
                            (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                                  (nb072AlphaDummy051 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0046 A B R S_cls H) 1))))
                              (show x ≠ (nb072AlphaDummy053 x H) from (by
                                  unfold nb072AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                          1)))) (TAlphaVar.there (show
                                  (nb072AlphaDummy000 A B R S_cls H) ≠
                                    (nb072AlphaDummy050 A B R S_cls H) from (by
                                    unfold nb072AlphaDummy050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0046 A B R S_cls H) 0))))
                                (show x ≠ (nb072AlphaDummy052 x H) from (by
                                    unfold nb072AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                            0)))) (TAlphaVar.there (show
                                    (nb072AlphaDummy000 A B R S_cls H) ≠
                                      (nb072AlphaDummy039 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy039;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0038 A B R S_cls H) 1))))
                                  (show x ≠ (nb072AlphaDummy041 x y H) from (by
                                      unfold nb072AlphaDummy041;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0040 x y H) 1))))
                                  (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                                        (nb072AlphaDummy038 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy038;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0038 A B R S_cls H)
                                                0))))
                                    (show x ≠ (nb072AlphaDummy040 x y H) from (by
                                        unfold nb072AlphaDummy040;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0040 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy000 A B R S_cls H) ≠
        (nb072AlphaDummy044 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy044;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0042 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072AlphaDummy045 x y H) from (by
                                          unfold nb072AlphaDummy045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0043 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy042 A B R S_cls H) from (by
          unfold nb072AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0039 A B R S_cls H)
                  0)))) (show x ≠ (nb072AlphaDummy043 x y H) from (by
          unfold nb072AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0041 x y H) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
                      ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb072AlphaDummy055 A B R S_cls H) ≠
                              (nb072AlphaDummy062 A B R S_cls H) from (by
                              unfold nb072AlphaDummy062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0056 A B R S_cls H) 0))))
                          (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy064 x H) from
                            (by
                              unfold nb072AlphaDummy064;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0057 x H) 0))))
                          (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                                (nb072AlphaDummy063 A B R S_cls H) from (by
                                unfold nb072AlphaDummy063;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0056 A B R S_cls H) 1)))) (show
                              (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy065 x H) from (by
                                unfold nb072AlphaDummy065;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0057 x H) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb072AlphaDummy057 x H))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy069 A B R S_cls H) from (by
          unfold nb072AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy072 x H) from (by
          unfold nb072AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H) 1)))) (TAlphaVar.there (show
        (nb072AlphaDummy062 A B R S_cls H) ≠ (nb072AlphaDummy068 A B R S_cls H) from (by
          unfold nb072AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy071 x H) from (by
          unfold nb072AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy066 A B R S_cls H) from (by
          unfold nb072AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from (by
          unfold nb072AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy070 A B R S_cls H), (nb072AlphaDummy073 x H)),
        ((nb072AlphaDummy069 A B R S_cls H), (nb072AlphaDummy072 x H)),
        ((nb072AlphaDummy068 A B R S_cls H), (nb072AlphaDummy071 x H)),
        ((nb072AlphaDummy066 A B R S_cls H), (nb072AlphaDummy067 x H)),
        ((nb072AlphaDummy062 A B R S_cls H), (nb072AlphaDummy064 x H)),
        ((nb072AlphaDummy063 A B R S_cls H), (nb072AlphaDummy065 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy060 A B R S_cls H), (nb072AlphaDummy061 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy070 A B R S_cls H), (nb072AlphaDummy073 x H)),
        ((nb072AlphaDummy069 A B R S_cls H), (nb072AlphaDummy072 x H)),
        ((nb072AlphaDummy068 A B R S_cls H), (nb072AlphaDummy071 x H)),
        ((nb072AlphaDummy066 A B R S_cls H), (nb072AlphaDummy067 x H)),
        ((nb072AlphaDummy062 A B R S_cls H), (nb072AlphaDummy064 x H)),
        ((nb072AlphaDummy063 A B R S_cls H), (nb072AlphaDummy065 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy060 A B R S_cls H), (nb072AlphaDummy061 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R
        S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy064 x
        H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy080
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy080
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy070
        A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy070
        A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy062 A B R S_cls H) ≠
                                        (nb072AlphaDummy066 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0058 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy064 x H) ≠
                                        (nb072AlphaDummy067 x H) from (by
                                        unfold nb072AlphaDummy067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0059 x H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb072AlphaDummy066 A B R S_cls H),
                                      (nb072AlphaDummy067 x H)),
                                    ((nb072AlphaDummy062 A B R S_cls H),
                                      (nb072AlphaDummy064 x H)),
                                    ((nb072AlphaDummy063 A B R S_cls H),
                                      (nb072AlphaDummy065 x H)),
                                    ((nb072AlphaDummy055 A B R S_cls H),
                                      (nb072AlphaDummy057 x H)),
                                    ((nb072AlphaDummy054 A B R S_cls H),
                                      (nb072AlphaDummy056 x H)),
                                    ((nb072AlphaDummy060 A B R S_cls H),
                                      (nb072AlphaDummy061 x H)),
                                    ((nb072AlphaDummy058 A B R S_cls H),
                                      (nb072AlphaDummy059 x H)),
                                    ((nb072AlphaDummy046 A B R S_cls H),
                                      (nb072AlphaDummy047 x H)),
                                    ((nb072AlphaDummy048 A B R S_cls H),
                                      (nb072AlphaDummy049 x H)),
                                    ((nb072AlphaDummy051 A B R S_cls H),
                                      (nb072AlphaDummy053 x H)),
                                    ((nb072AlphaDummy050 A B R S_cls H),
                                      (nb072AlphaDummy052 x H)),
                                    ((nb072AlphaDummy039 A B R S_cls H),
                                      (nb072AlphaDummy041 x y H)),
                                    ((nb072AlphaDummy038 A B R S_cls H),
                                      (nb072AlphaDummy040 x y H)),
                                    ((nb072AlphaDummy044 A B R S_cls H),
                                      (nb072AlphaDummy045 x y H)),
                                    ((nb072AlphaDummy042 A B R S_cls H),
                                      (nb072AlphaDummy043 x y H)),
                                    ((nb072AlphaDummy001 A B R S_cls H), y),
                                    ((nb072AlphaDummy000 A B R S_cls H), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072AlphaDummy062 A B R S_cls H) ≠
                                      (nb072AlphaDummy066 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                                    (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H)
                                    from (by
                                      unfold nb072AlphaDummy067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0059 x H)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy062 A B R S_cls H) ≠
                                        (nb072AlphaDummy066 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0058 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy064 x H) ≠
                                        (nb072AlphaDummy067 x H) from (by
                                        unfold nb072AlphaDummy067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0059 x H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb072AlphaDummy066 A B R S_cls H),
                                      (nb072AlphaDummy067 x H)),
                                    ((nb072AlphaDummy062 A B R S_cls H),
                                      (nb072AlphaDummy064 x H)),
                                    ((nb072AlphaDummy063 A B R S_cls H),
                                      (nb072AlphaDummy065 x H)),
                                    ((nb072AlphaDummy055 A B R S_cls H),
                                      (nb072AlphaDummy057 x H)),
                                    ((nb072AlphaDummy054 A B R S_cls H),
                                      (nb072AlphaDummy056 x H)),
                                    ((nb072AlphaDummy060 A B R S_cls H),
                                      (nb072AlphaDummy061 x H)),
                                    ((nb072AlphaDummy058 A B R S_cls H),
                                      (nb072AlphaDummy059 x H)),
                                    ((nb072AlphaDummy046 A B R S_cls H),
                                      (nb072AlphaDummy047 x H)),
                                    ((nb072AlphaDummy048 A B R S_cls H),
                                      (nb072AlphaDummy049 x H)),
                                    ((nb072AlphaDummy051 A B R S_cls H),
                                      (nb072AlphaDummy053 x H)),
                                    ((nb072AlphaDummy050 A B R S_cls H),
                                      (nb072AlphaDummy052 x H)),
                                    ((nb072AlphaDummy039 A B R S_cls H),
                                      (nb072AlphaDummy041 x y H)),
                                    ((nb072AlphaDummy038 A B R S_cls H),
                                      (nb072AlphaDummy040 x y H)),
                                    ((nb072AlphaDummy044 A B R S_cls H),
                                      (nb072AlphaDummy045 x y H)),
                                    ((nb072AlphaDummy042 A B R S_cls H),
                                      (nb072AlphaDummy043 x y H)),
                                    ((nb072AlphaDummy001 A B R S_cls H), y),
                                    ((nb072AlphaDummy000 A B R S_cls H), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                        (nb072AlphaDummy055 A B R S_cls H) from (by
                        unfold nb072AlphaDummy055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H)
                                1)))) (show x ≠ (nb072AlphaDummy057 x H) from (by
                        unfold nb072AlphaDummy057;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))))
                    (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                          (nb072AlphaDummy054 A B R S_cls H) from (by
                          unfold nb072AlphaDummy054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H)
                                  0)))) (show x ≠ (nb072AlphaDummy056 x H) from (by
                          unfold nb072AlphaDummy056;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
                      (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                            (nb072AlphaDummy060 A B R S_cls H) from (by
                            unfold nb072AlphaDummy060;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0054 A B R S_cls H)
                                    0)))) (show x ≠ (nb072AlphaDummy061 x H) from (by
                            unfold nb072AlphaDummy061;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0055 x H) 0))))
                        (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                              (nb072AlphaDummy058 A B R S_cls H) from (by
                              unfold nb072AlphaDummy058;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0051 A B R S_cls H) 0))))
                          (show x ≠ (nb072AlphaDummy059 x H) from (by
                              unfold nb072AlphaDummy059;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0053 x H) 0))))
                          (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                                (nb072AlphaDummy046 A B R S_cls H) from (by
                                unfold nb072AlphaDummy046;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0044 A B R S_cls H) 0))))
                            (show x ≠ (nb072AlphaDummy047 x H) from (by
                                unfold nb072AlphaDummy047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0047 x H) 0))))
                            (TAlphaVar.there (show (nb072AlphaDummy000 A B R S_cls H) ≠
                                  (nb072AlphaDummy048 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0045 A B R S_cls H) 0))))
                              (show x ≠ (nb072AlphaDummy049 x H) from (by
                                  unfold nb072AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0048 x H)
                                          0)))) (TAlphaVar.there (show
                                  (nb072AlphaDummy000 A B R S_cls H) ≠
                                    (nb072AlphaDummy051 A B R S_cls H) from (by
                                    unfold nb072AlphaDummy051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0046 A B R S_cls H) 1))))
                                (show x ≠ (nb072AlphaDummy053 x H) from (by
                                    unfold nb072AlphaDummy053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                            1)))) (TAlphaVar.there (show
                                    (nb072AlphaDummy000 A B R S_cls H) ≠
                                      (nb072AlphaDummy050 A B R S_cls H) from (by
                                      unfold nb072AlphaDummy050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0046 A B R S_cls H) 0))))
                                  (show x ≠ (nb072AlphaDummy052 x H) from (by
                                      unfold nb072AlphaDummy052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                              0)))) (TAlphaVar.there (show
                                      (nb072AlphaDummy000 A B R S_cls H) ≠
                                        (nb072AlphaDummy039 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy039;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0038 A B R S_cls H)
                                                1))))
                                    (show x ≠ (nb072AlphaDummy041 x y H) from (by
                                        unfold nb072AlphaDummy041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0040 x y H) 1))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy000 A B R S_cls H) ≠
        (nb072AlphaDummy038 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy038;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0038 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072AlphaDummy040 x y H) from (by
                                          unfold nb072AlphaDummy040;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0040 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy044 A B R S_cls H) from (by
          unfold nb072AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0042 A B R S_cls H)
                  0)))) (show x ≠ (nb072AlphaDummy045 x y H) from (by
          unfold nb072AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0043 x y H) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy000 A B R S_cls H) ≠ (nb072AlphaDummy042 A B R S_cls H) from (by
          unfold nb072AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0039 A B R S_cls
                    H)
                  0)))) (show x ≠ (nb072AlphaDummy043 x y H) from (by
          unfold nb072AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0041 x y H) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv ∪
                        ((Class.cv (nb072AlphaDummy046 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv x)).fv ∪ ((Class.cv (nb072AlphaDummy047 x H))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072AlphaDummy055 A B R S_cls H) ≠
                                (nb072AlphaDummy062 A B R S_cls H) from (by
                                unfold nb072AlphaDummy062;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0056 A B R S_cls H) 0)))) (show
                              (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy064 x H) from (by
                                unfold nb072AlphaDummy064;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0057 x H) 0))))
                            (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                                  (nb072AlphaDummy063 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy063;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0056 A B R S_cls H) 1)))) (show
                                (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy065 x H) from
                                (by
                                  unfold nb072AlphaDummy065;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0057 x H)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb072AlphaDummy057 x H))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy062 A B R S_cls H) ≠ (nb072AlphaDummy069 A B R S_cls H) from (by
          unfold nb072AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  1)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy072 x H) from (by
          unfold nb072AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H)
                  1)))) (TAlphaVar.there (show (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy068 A B R S_cls H) from (by
          unfold nb072AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy071 x H) from (by
          unfold nb072AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy066 A B R S_cls H) from (by
          unfold nb072AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B
                    R S_cls H)
                  0)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from (by
          unfold nb072AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy070 A B R S_cls H), (nb072AlphaDummy073 x H)),
        ((nb072AlphaDummy069 A B R S_cls H), (nb072AlphaDummy072 x H)),
        ((nb072AlphaDummy068 A B R S_cls H), (nb072AlphaDummy071 x H)),
        ((nb072AlphaDummy066 A B R S_cls H), (nb072AlphaDummy067 x H)),
        ((nb072AlphaDummy062 A B R S_cls H), (nb072AlphaDummy064 x H)),
        ((nb072AlphaDummy063 A B R S_cls H), (nb072AlphaDummy065 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy060 A B R S_cls H), (nb072AlphaDummy061 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy076
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy070 A B R S_cls H), (nb072AlphaDummy073 x H)),
        ((nb072AlphaDummy069 A B R S_cls H), (nb072AlphaDummy072 x H)),
        ((nb072AlphaDummy068 A B R S_cls H), (nb072AlphaDummy071 x H)),
        ((nb072AlphaDummy066 A B R S_cls H), (nb072AlphaDummy067 x H)),
        ((nb072AlphaDummy062 A B R S_cls H), (nb072AlphaDummy064 x H)),
        ((nb072AlphaDummy063 A B R S_cls H), (nb072AlphaDummy065 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy060 A B R S_cls H), (nb072AlphaDummy061 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R
        S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072AlphaDummy064 x
        H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy080
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy080
        A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy070
        A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy070
        A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy066 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0058 A B R S_cls H)
                                                  0)))) (show (nb072AlphaDummy064 x H) ≠
        (nb072AlphaDummy067 x H) from (by
                                          unfold nb072AlphaDummy067;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0059 x H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb072AlphaDummy066 A B R S_cls H),
                                        (nb072AlphaDummy067 x H)),
                                      ((nb072AlphaDummy062 A B R S_cls H),
                                        (nb072AlphaDummy064 x H)),
                                      ((nb072AlphaDummy063 A B R S_cls H),
                                        (nb072AlphaDummy065 x H)),
                                      ((nb072AlphaDummy055 A B R S_cls H),
                                        (nb072AlphaDummy057 x H)),
                                      ((nb072AlphaDummy054 A B R S_cls H),
                                        (nb072AlphaDummy056 x H)),
                                      ((nb072AlphaDummy060 A B R S_cls H),
                                        (nb072AlphaDummy061 x H)),
                                      ((nb072AlphaDummy058 A B R S_cls H),
                                        (nb072AlphaDummy059 x H)),
                                      ((nb072AlphaDummy046 A B R S_cls H),
                                        (nb072AlphaDummy047 x H)),
                                      ((nb072AlphaDummy048 A B R S_cls H),
                                        (nb072AlphaDummy049 x H)),
                                      ((nb072AlphaDummy051 A B R S_cls H),
                                        (nb072AlphaDummy053 x H)),
                                      ((nb072AlphaDummy050 A B R S_cls H),
                                        (nb072AlphaDummy052 x H)),
                                      ((nb072AlphaDummy039 A B R S_cls H),
                                        (nb072AlphaDummy041 x y H)),
                                      ((nb072AlphaDummy038 A B R S_cls H),
                                        (nb072AlphaDummy040 x y H)),
                                      ((nb072AlphaDummy044 A B R S_cls H),
                                        (nb072AlphaDummy045 x y H)),
                                      ((nb072AlphaDummy042 A B R S_cls H),
                                        (nb072AlphaDummy043 x y H)),
                                      ((nb072AlphaDummy001 A B R S_cls H), y),
                                      ((nb072AlphaDummy000 A B R S_cls H), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy062 A B R S_cls H) ≠
                                        (nb072AlphaDummy066 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0058 A B R S_cls H)
                                                0)))) (show (nb072AlphaDummy064 x H) ≠
                                        (nb072AlphaDummy067 x H) from (by
                                        unfold nb072AlphaDummy067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0059 x H) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy066 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0058 A B R S_cls H)
                                                  0)))) (show (nb072AlphaDummy064 x H) ≠
        (nb072AlphaDummy067 x H) from (by
                                          unfold nb072AlphaDummy067;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0059 x H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb072AlphaDummy066 A B R S_cls H),
                                        (nb072AlphaDummy067 x H)),
                                      ((nb072AlphaDummy062 A B R S_cls H),
                                        (nb072AlphaDummy064 x H)),
                                      ((nb072AlphaDummy063 A B R S_cls H),
                                        (nb072AlphaDummy065 x H)),
                                      ((nb072AlphaDummy055 A B R S_cls H),
                                        (nb072AlphaDummy057 x H)),
                                      ((nb072AlphaDummy054 A B R S_cls H),
                                        (nb072AlphaDummy056 x H)),
                                      ((nb072AlphaDummy060 A B R S_cls H),
                                        (nb072AlphaDummy061 x H)),
                                      ((nb072AlphaDummy058 A B R S_cls H),
                                        (nb072AlphaDummy059 x H)),
                                      ((nb072AlphaDummy046 A B R S_cls H),
                                        (nb072AlphaDummy047 x H)),
                                      ((nb072AlphaDummy048 A B R S_cls H),
                                        (nb072AlphaDummy049 x H)),
                                      ((nb072AlphaDummy051 A B R S_cls H),
                                        (nb072AlphaDummy053 x H)),
                                      ((nb072AlphaDummy050 A B R S_cls H),
                                        (nb072AlphaDummy052 x H)),
                                      ((nb072AlphaDummy039 A B R S_cls H),
                                        (nb072AlphaDummy041 x y H)),
                                      ((nb072AlphaDummy038 A B R S_cls H),
                                        (nb072AlphaDummy040 x y H)),
                                      ((nb072AlphaDummy044 A B R S_cls H),
                                        (nb072AlphaDummy045 x y H)),
                                      ((nb072AlphaDummy042 A B R S_cls H),
                                        (nb072AlphaDummy043 x y H)),
                                      ((nb072AlphaDummy001 A B R S_cls H), y),
                                      ((nb072AlphaDummy000 A B R S_cls H), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part010`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb072_split_alpha_0002`. -/
@[expose]
noncomputable def nb072SplitAlpha0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) :
    TAlphaWff
      [((nb072AlphaDummy088 A B R S_cls H), (nb072AlphaDummy089 x H)),
        ((nb072AlphaDummy086 A B R S_cls H), (nb072AlphaDummy087 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy084 A B R S_cls H), (nb072AlphaDummy085 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy088 A B R S_cls H))
          (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H)))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy088 A B R S_cls H))
            (synCphi (Class.cv (nb072AlphaDummy055 A B R S_cls H))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072AlphaDummy089 x H))
          (synCphi (Class.cv (nb072AlphaDummy057 x H)))) (Wff.neg
          (Wff.classMem (Class.cv (nb072AlphaDummy089 x H))
            (synCphi (Class.cv (nb072AlphaDummy057 x H)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                      (nb072AlphaDummy062 A B R S_cls H) from (by
                      unfold nb072AlphaDummy062;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H) 0))))
                  (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy064 x H) from (by
                      unfold nb072AlphaDummy064;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0057 x H) 0)))) (TAlphaVar.there
                    (show (nb072AlphaDummy055 A B R S_cls H) ≠
                        (nb072AlphaDummy063 A B R S_cls H) from (by
                        unfold nb072AlphaDummy063;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H)
                                1))))
                    (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy065 x H) from (by
                        unfold nb072AlphaDummy065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0057 x H) 1))))
                    (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                          (nb072AlphaDummy088 A B R S_cls H) from (by
                          unfold nb072AlphaDummy088;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0086 A B R S_cls H)
                                  0))))
                      (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy089 x H) from (by
                          unfold nb072AlphaDummy089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0087 x H) 0))))
                      (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                            (nb072AlphaDummy086 A B R S_cls H) from (by
                            unfold nb072AlphaDummy086;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0084 A B R S_cls H)
                                    0))))
                        (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy087 x H) from (by
                            unfold nb072AlphaDummy087;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0085 x H) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb072AlphaDummy057 x H))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072AlphaDummy062 A B R S_cls H) ≠
                                        (nb072AlphaDummy069 A B R S_cls H) from (by
                                        unfold nb072AlphaDummy069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0060 A B R S_cls H)
                                                1)))) (show (nb072AlphaDummy064 x H) ≠
                                        (nb072AlphaDummy072 x H) from (by
                                        unfold nb072AlphaDummy072;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0061 x H) 1))))
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy068 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy068;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0060 A B R S_cls H)
                                                  0)))) (show (nb072AlphaDummy064 x H) ≠
        (nb072AlphaDummy071 x H) from (by
                                          unfold nb072AlphaDummy071;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0061 x H) 0))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy062 A B R S_cls H) ≠ (nb072AlphaDummy066 A B R S_cls H) from (by
          unfold nb072AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B R S_cls H)
                  0)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from (by
          unfold nb072AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb072AlphaDummy070 A B R S_cls H),
        (nb072AlphaDummy073 x H)), ((nb072AlphaDummy069 A B R S_cls H),
        (nb072AlphaDummy072 x H)), ((nb072AlphaDummy068 A B R S_cls H),
        (nb072AlphaDummy071 x H)), ((nb072AlphaDummy066 A B R S_cls H),
        (nb072AlphaDummy067 x H)), ((nb072AlphaDummy062 A B R S_cls H),
        (nb072AlphaDummy064 x H)), ((nb072AlphaDummy063 A B R S_cls H),
        (nb072AlphaDummy065 x H)), ((nb072AlphaDummy088 A B R S_cls H),
        (nb072AlphaDummy089 x H)), ((nb072AlphaDummy086 A B R S_cls H),
        (nb072AlphaDummy087 x H)), ((nb072AlphaDummy055 A B R S_cls H),
        (nb072AlphaDummy057 x H)), ((nb072AlphaDummy054 A B R S_cls H),
        (nb072AlphaDummy056 x H)), ((nb072AlphaDummy084 A B R S_cls H),
        (nb072AlphaDummy085 x H)), ((nb072AlphaDummy058 A B R S_cls H),
        (nb072AlphaDummy059 x H)), ((nb072AlphaDummy046 A B R S_cls H),
        (nb072AlphaDummy047 x H)), ((nb072AlphaDummy048 A B R S_cls H),
        (nb072AlphaDummy049 x H)), ((nb072AlphaDummy051 A B R S_cls H),
        (nb072AlphaDummy053 x H)), ((nb072AlphaDummy050 A B R S_cls H),
        (nb072AlphaDummy052 x H)), ((nb072AlphaDummy039 A B R S_cls H),
        (nb072AlphaDummy041 x y H)), ((nb072AlphaDummy038 A B R S_cls H),
        (nb072AlphaDummy040 x y H)), ((nb072AlphaDummy044 A B R S_cls H),
        (nb072AlphaDummy045 x y H)), ((nb072AlphaDummy042 A B R S_cls H),
        (nb072AlphaDummy043 x y H)), ((nb072AlphaDummy001 A B R S_cls H), y),
                                        ((nb072AlphaDummy000 A B R S_cls H), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb072AlphaDummy070 A B R S_cls H),
        (nb072AlphaDummy073 x H)), ((nb072AlphaDummy069 A B R S_cls H),
        (nb072AlphaDummy072 x H)), ((nb072AlphaDummy068 A B R S_cls H),
        (nb072AlphaDummy071 x H)), ((nb072AlphaDummy066 A B R S_cls H),
        (nb072AlphaDummy067 x H)), ((nb072AlphaDummy062 A B R S_cls H),
        (nb072AlphaDummy064 x H)), ((nb072AlphaDummy063 A B R S_cls H),
        (nb072AlphaDummy065 x H)), ((nb072AlphaDummy088 A B R S_cls H),
        (nb072AlphaDummy089 x H)), ((nb072AlphaDummy086 A B R S_cls H),
        (nb072AlphaDummy087 x H)), ((nb072AlphaDummy055 A B R S_cls H),
        (nb072AlphaDummy057 x H)), ((nb072AlphaDummy054 A B R S_cls H),
        (nb072AlphaDummy056 x H)), ((nb072AlphaDummy084 A B R S_cls H),
        (nb072AlphaDummy085 x H)), ((nb072AlphaDummy058 A B R S_cls H),
        (nb072AlphaDummy059 x H)), ((nb072AlphaDummy046 A B R S_cls H),
        (nb072AlphaDummy047 x H)), ((nb072AlphaDummy048 A B R S_cls H),
        (nb072AlphaDummy049 x H)), ((nb072AlphaDummy051 A B R S_cls H),
        (nb072AlphaDummy053 x H)), ((nb072AlphaDummy050 A B R S_cls H),
        (nb072AlphaDummy052 x H)), ((nb072AlphaDummy039 A B R S_cls H),
        (nb072AlphaDummy041 x y H)), ((nb072AlphaDummy038 A B R S_cls H),
        (nb072AlphaDummy040 x y H)), ((nb072AlphaDummy044 A B R S_cls H),
        (nb072AlphaDummy045 x y H)), ((nb072AlphaDummy042 A B R S_cls H),
        (nb072AlphaDummy043 x y H)), ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)] (synC0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R S_cls
        H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy080 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy080 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072AlphaDummy062 A B R S_cls H) ≠
                                (nb072AlphaDummy066 A B R S_cls H) from (by
                                unfold nb072AlphaDummy066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                              (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from (by
                                unfold nb072AlphaDummy067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb072AlphaDummy066 A B R S_cls H), (nb072AlphaDummy067 x H)),
                            ((nb072AlphaDummy062 A B R S_cls H),
                              (nb072AlphaDummy064 x H)),
                            ((nb072AlphaDummy063 A B R S_cls H),
                              (nb072AlphaDummy065 x H)),
                            ((nb072AlphaDummy088 A B R S_cls H),
                              (nb072AlphaDummy089 x H)),
                            ((nb072AlphaDummy086 A B R S_cls H),
                              (nb072AlphaDummy087 x H)),
                            ((nb072AlphaDummy055 A B R S_cls H),
                              (nb072AlphaDummy057 x H)),
                            ((nb072AlphaDummy054 A B R S_cls H),
                              (nb072AlphaDummy056 x H)),
                            ((nb072AlphaDummy084 A B R S_cls H),
                              (nb072AlphaDummy085 x H)),
                            ((nb072AlphaDummy058 A B R S_cls H),
                              (nb072AlphaDummy059 x H)),
                            ((nb072AlphaDummy046 A B R S_cls H),
                              (nb072AlphaDummy047 x H)),
                            ((nb072AlphaDummy048 A B R S_cls H),
                              (nb072AlphaDummy049 x H)),
                            ((nb072AlphaDummy051 A B R S_cls H),
                              (nb072AlphaDummy053 x H)),
                            ((nb072AlphaDummy050 A B R S_cls H),
                              (nb072AlphaDummy052 x H)),
                            ((nb072AlphaDummy039 A B R S_cls H),
                              (nb072AlphaDummy041 x y H)),
                            ((nb072AlphaDummy038 A B R S_cls H),
                              (nb072AlphaDummy040 x y H)),
                            ((nb072AlphaDummy044 A B R S_cls H),
                              (nb072AlphaDummy045 x y H)),
                            ((nb072AlphaDummy042 A B R S_cls H),
                              (nb072AlphaDummy043 x y H)),
                            ((nb072AlphaDummy001 A B R S_cls H), y),
                            ((nb072AlphaDummy000 A B R S_cls H), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb072AlphaDummy062 A B R S_cls H) ≠
                              (nb072AlphaDummy066 A B R S_cls H) from (by
                              unfold nb072AlphaDummy066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0058 A B R S_cls H) 0))))
                          (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from
                            (by
                              unfold nb072AlphaDummy067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072AlphaDummy062 A B R S_cls H) ≠
                                (nb072AlphaDummy066 A B R S_cls H) from (by
                                unfold nb072AlphaDummy066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                              (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from (by
                                unfold nb072AlphaDummy067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb072AlphaDummy066 A B R S_cls H), (nb072AlphaDummy067 x H)),
                            ((nb072AlphaDummy062 A B R S_cls H),
                              (nb072AlphaDummy064 x H)),
                            ((nb072AlphaDummy063 A B R S_cls H),
                              (nb072AlphaDummy065 x H)),
                            ((nb072AlphaDummy088 A B R S_cls H),
                              (nb072AlphaDummy089 x H)),
                            ((nb072AlphaDummy086 A B R S_cls H),
                              (nb072AlphaDummy087 x H)),
                            ((nb072AlphaDummy055 A B R S_cls H),
                              (nb072AlphaDummy057 x H)),
                            ((nb072AlphaDummy054 A B R S_cls H),
                              (nb072AlphaDummy056 x H)),
                            ((nb072AlphaDummy084 A B R S_cls H),
                              (nb072AlphaDummy085 x H)),
                            ((nb072AlphaDummy058 A B R S_cls H),
                              (nb072AlphaDummy059 x H)),
                            ((nb072AlphaDummy046 A B R S_cls H),
                              (nb072AlphaDummy047 x H)),
                            ((nb072AlphaDummy048 A B R S_cls H),
                              (nb072AlphaDummy049 x H)),
                            ((nb072AlphaDummy051 A B R S_cls H),
                              (nb072AlphaDummy053 x H)),
                            ((nb072AlphaDummy050 A B R S_cls H),
                              (nb072AlphaDummy052 x H)),
                            ((nb072AlphaDummy039 A B R S_cls H),
                              (nb072AlphaDummy041 x y H)),
                            ((nb072AlphaDummy038 A B R S_cls H),
                              (nb072AlphaDummy040 x y H)),
                            ((nb072AlphaDummy044 A B R S_cls H),
                              (nb072AlphaDummy045 x y H)),
                            ((nb072AlphaDummy042 A B R S_cls H),
                              (nb072AlphaDummy043 x y H)),
                            ((nb072AlphaDummy001 A B R S_cls H), y),
                            ((nb072AlphaDummy000 A B R S_cls H), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                        (nb072AlphaDummy062 A B R S_cls H) from (by
                        unfold nb072AlphaDummy062;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H)
                                0))))
                    (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy064 x H) from (by
                        unfold nb072AlphaDummy064;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0057 x H) 0))))
                    (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                          (nb072AlphaDummy063 A B R S_cls H) from (by
                          unfold nb072AlphaDummy063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H)
                                  1))))
                      (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy065 x H) from (by
                          unfold nb072AlphaDummy065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0057 x H) 1))))
                      (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                            (nb072AlphaDummy088 A B R S_cls H) from (by
                            unfold nb072AlphaDummy088;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0086 A B R S_cls H)
                                    0))))
                        (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy089 x H) from (by
                            unfold nb072AlphaDummy089;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0087 x H) 0))))
                        (TAlphaVar.there (show (nb072AlphaDummy055 A B R S_cls H) ≠
                              (nb072AlphaDummy086 A B R S_cls H) from (by
                              unfold nb072AlphaDummy086;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0084 A B R S_cls H) 0))))
                          (show (nb072AlphaDummy057 x H) ≠ (nb072AlphaDummy087 x H) from
                            (by
                              unfold nb072AlphaDummy087;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0085 x H) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072AlphaDummy055 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb072AlphaDummy057 x H))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb072AlphaDummy062 A B R S_cls H) ≠
        (nb072AlphaDummy069 A B R S_cls H) from (by
                                          unfold nb072AlphaDummy069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0060 A B R S_cls H)
                                                  1)))) (show (nb072AlphaDummy064 x H) ≠
        (nb072AlphaDummy072 x H) from (by
                                          unfold nb072AlphaDummy072;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0061 x H) 1))))
                                      (TAlphaVar.there (show
        (nb072AlphaDummy062 A B R S_cls H) ≠ (nb072AlphaDummy068 A B R S_cls H) from (by
          unfold nb072AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R S_cls H)
                  0)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy071 x H) from (by
          unfold nb072AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H) 0)))) (TAlphaVar.there (show
        (nb072AlphaDummy062 A B R S_cls H) ≠ (nb072AlphaDummy066 A B R S_cls H) from (by
          unfold nb072AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B R S_cls
                    H)
                  0)))) (show (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from (by
          unfold nb072AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb072AlphaDummy070 A B R S_cls H),
        (nb072AlphaDummy073 x H)), ((nb072AlphaDummy069 A B R S_cls H),
        (nb072AlphaDummy072 x H)), ((nb072AlphaDummy068 A B R S_cls H),
        (nb072AlphaDummy071 x H)), ((nb072AlphaDummy066 A B R S_cls H),
        (nb072AlphaDummy067 x H)), ((nb072AlphaDummy062 A B R S_cls H),
        (nb072AlphaDummy064 x H)), ((nb072AlphaDummy063 A B R S_cls H),
        (nb072AlphaDummy065 x H)), ((nb072AlphaDummy088 A B R S_cls H),
        (nb072AlphaDummy089 x H)), ((nb072AlphaDummy086 A B R S_cls H),
        (nb072AlphaDummy087 x H)), ((nb072AlphaDummy055 A B R S_cls H),
        (nb072AlphaDummy057 x H)), ((nb072AlphaDummy054 A B R S_cls H),
        (nb072AlphaDummy056 x H)), ((nb072AlphaDummy084 A B R S_cls H),
        (nb072AlphaDummy085 x H)), ((nb072AlphaDummy058 A B R S_cls H),
        (nb072AlphaDummy059 x H)), ((nb072AlphaDummy046 A B R S_cls H),
        (nb072AlphaDummy047 x H)), ((nb072AlphaDummy048 A B R S_cls H),
        (nb072AlphaDummy049 x H)), ((nb072AlphaDummy051 A B R S_cls H),
        (nb072AlphaDummy053 x H)), ((nb072AlphaDummy050 A B R S_cls H),
        (nb072AlphaDummy052 x H)), ((nb072AlphaDummy039 A B R S_cls H),
        (nb072AlphaDummy041 x y H)), ((nb072AlphaDummy038 A B R S_cls H),
        (nb072AlphaDummy040 x y H)), ((nb072AlphaDummy044 A B R S_cls H),
        (nb072AlphaDummy045 x y H)), ((nb072AlphaDummy042 A B R S_cls H),
        (nb072AlphaDummy043 x y H)), ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy076 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy077 x H) from (by
          unfold
            nb072AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy074 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy075 x H) from (by
          unfold
            nb072AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb072AlphaDummy070 A B R S_cls H), (nb072AlphaDummy073 x H)),
        ((nb072AlphaDummy069 A B R S_cls H), (nb072AlphaDummy072 x H)),
        ((nb072AlphaDummy068 A B R S_cls H), (nb072AlphaDummy071 x H)),
        ((nb072AlphaDummy066 A B R S_cls H), (nb072AlphaDummy067 x H)),
        ((nb072AlphaDummy062 A B R S_cls H), (nb072AlphaDummy064 x H)),
        ((nb072AlphaDummy063 A B R S_cls H), (nb072AlphaDummy065 x H)),
        ((nb072AlphaDummy088 A B R S_cls H), (nb072AlphaDummy089 x H)),
        ((nb072AlphaDummy086 A B R S_cls H), (nb072AlphaDummy087 x H)),
        ((nb072AlphaDummy055 A B R S_cls H), (nb072AlphaDummy057 x H)),
        ((nb072AlphaDummy054 A B R S_cls H), (nb072AlphaDummy056 x H)),
        ((nb072AlphaDummy084 A B R S_cls H), (nb072AlphaDummy085 x H)),
        ((nb072AlphaDummy058 A B R S_cls H), (nb072AlphaDummy059 x H)),
        ((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y), ((nb072AlphaDummy000 A B R S_cls H), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R S_cls
        H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072AlphaDummy062 A B R S_cls H))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy069 A B R S_cls H) ≠ (nb072AlphaDummy080 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy080 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy081 x H) from (by
          unfold
            nb072AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy069 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy072 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072AlphaDummy062
        A B R S_cls H))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072AlphaDummy064 x H))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072AlphaDummy070 A B R S_cls H) ≠ (nb072AlphaDummy082 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy083 x H) from (by
          unfold
            nb072AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072AlphaDummy070 A B R S_cls H) ≠
        (nb072AlphaDummy078 A B R S_cls H) from (by
          unfold
            nb072AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072AlphaDummy073 x H) ≠ (nb072AlphaDummy079 x H) from (by
          unfold
            nb072AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb072AlphaDummy062 A B R S_cls H) ≠
                                  (nb072AlphaDummy066 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                                (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from
                                (by
                                  unfold nb072AlphaDummy067;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0059 x H)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed [((nb072AlphaDummy066 A B R S_cls H),
                                (nb072AlphaDummy067 x H)),
                              ((nb072AlphaDummy062 A B R S_cls H),
                                (nb072AlphaDummy064 x H)),
                              ((nb072AlphaDummy063 A B R S_cls H),
                                (nb072AlphaDummy065 x H)),
                              ((nb072AlphaDummy088 A B R S_cls H),
                                (nb072AlphaDummy089 x H)),
                              ((nb072AlphaDummy086 A B R S_cls H),
                                (nb072AlphaDummy087 x H)),
                              ((nb072AlphaDummy055 A B R S_cls H),
                                (nb072AlphaDummy057 x H)),
                              ((nb072AlphaDummy054 A B R S_cls H),
                                (nb072AlphaDummy056 x H)),
                              ((nb072AlphaDummy084 A B R S_cls H),
                                (nb072AlphaDummy085 x H)),
                              ((nb072AlphaDummy058 A B R S_cls H),
                                (nb072AlphaDummy059 x H)),
                              ((nb072AlphaDummy046 A B R S_cls H),
                                (nb072AlphaDummy047 x H)),
                              ((nb072AlphaDummy048 A B R S_cls H),
                                (nb072AlphaDummy049 x H)),
                              ((nb072AlphaDummy051 A B R S_cls H),
                                (nb072AlphaDummy053 x H)),
                              ((nb072AlphaDummy050 A B R S_cls H),
                                (nb072AlphaDummy052 x H)),
                              ((nb072AlphaDummy039 A B R S_cls H),
                                (nb072AlphaDummy041 x y H)),
                              ((nb072AlphaDummy038 A B R S_cls H),
                                (nb072AlphaDummy040 x y H)),
                              ((nb072AlphaDummy044 A B R S_cls H),
                                (nb072AlphaDummy045 x y H)),
                              ((nb072AlphaDummy042 A B R S_cls H),
                                (nb072AlphaDummy043 x y H)),
                              ((nb072AlphaDummy001 A B R S_cls H), y),
                              ((nb072AlphaDummy000 A B R S_cls H), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072AlphaDummy062 A B R S_cls H) ≠
                                (nb072AlphaDummy066 A B R S_cls H) from (by
                                unfold nb072AlphaDummy066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                              (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from (by
                                unfold nb072AlphaDummy067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb072AlphaDummy062 A B R S_cls H) ≠
                                  (nb072AlphaDummy066 A B R S_cls H) from (by
                                  unfold nb072AlphaDummy066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                                (nb072AlphaDummy064 x H) ≠ (nb072AlphaDummy067 x H) from
                                (by
                                  unfold nb072AlphaDummy067;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0059 x H)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed [((nb072AlphaDummy066 A B R S_cls H),
                                (nb072AlphaDummy067 x H)),
                              ((nb072AlphaDummy062 A B R S_cls H),
                                (nb072AlphaDummy064 x H)),
                              ((nb072AlphaDummy063 A B R S_cls H),
                                (nb072AlphaDummy065 x H)),
                              ((nb072AlphaDummy088 A B R S_cls H),
                                (nb072AlphaDummy089 x H)),
                              ((nb072AlphaDummy086 A B R S_cls H),
                                (nb072AlphaDummy087 x H)),
                              ((nb072AlphaDummy055 A B R S_cls H),
                                (nb072AlphaDummy057 x H)),
                              ((nb072AlphaDummy054 A B R S_cls H),
                                (nb072AlphaDummy056 x H)),
                              ((nb072AlphaDummy084 A B R S_cls H),
                                (nb072AlphaDummy085 x H)),
                              ((nb072AlphaDummy058 A B R S_cls H),
                                (nb072AlphaDummy059 x H)),
                              ((nb072AlphaDummy046 A B R S_cls H),
                                (nb072AlphaDummy047 x H)),
                              ((nb072AlphaDummy048 A B R S_cls H),
                                (nb072AlphaDummy049 x H)),
                              ((nb072AlphaDummy051 A B R S_cls H),
                                (nb072AlphaDummy053 x H)),
                              ((nb072AlphaDummy050 A B R S_cls H),
                                (nb072AlphaDummy052 x H)),
                              ((nb072AlphaDummy039 A B R S_cls H),
                                (nb072AlphaDummy041 x y H)),
                              ((nb072AlphaDummy038 A B R S_cls H),
                                (nb072AlphaDummy040 x y H)),
                              ((nb072AlphaDummy044 A B R S_cls H),
                                (nb072AlphaDummy045 x y H)),
                              ((nb072AlphaDummy042 A B R S_cls H),
                                (nb072AlphaDummy043 x y H)),
                              ((nb072AlphaDummy001 A B R S_cls H), y),
                              ((nb072AlphaDummy000 A B R S_cls H), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb072_focused_notmem_0004 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy046 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar ((H).fv ∪ ((Class.cv (nb072AlphaDummy000 A B R S_cls H))).fv) 0 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb072_focused_notmem_0005 (x : Var) (H : Class) :
    (nb072AlphaDummy047 x H) ∉ H.fv :=
  by
  change freshVar ((H).fv ∪ ((Class.cv x)).fv) 0 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb072_focused_notmem_0006 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy048 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (({(nb072AlphaDummy046 A B R S_cls H)} : Finset Var) ∪
          ((synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
              (Class.cv (nb072AlphaDummy046 A B R S_cls H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
      (Class.cv (nb072AlphaDummy046 A B R S_cls H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0007 (x : Var) (H : Class) :
    (nb072AlphaDummy049 x H) ∉ H.fv :=
  by
  change
    freshVar
        (({(nb072AlphaDummy047 x H)} : Finset Var) ∪
          ((synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0008 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy051 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
              (Class.cab (nb072AlphaDummy046 A B R S_cls H)
                (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                  (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
              (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb072AlphaDummy048 A B R S_cls H)
      (Wff.classEq (Class.cab (nb072AlphaDummy046 A B R S_cls H)
          (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
        (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0006 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072AlphaDummy046 A B R S_cls H)
          (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
        (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072AlphaDummy046 A B R S_cls H)
        (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
          (Class.cv (nb072AlphaDummy046 A B R S_cls H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0004 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
          (Class.cv (nb072AlphaDummy046 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0009 (x : Var) (H : Class) :
    (nb072AlphaDummy053 x H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
              (Class.cab (nb072AlphaDummy047 x H)
                (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
              (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb072AlphaDummy049 x H)
      (Wff.classEq (Class.cab (nb072AlphaDummy047 x H)
          (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
        (synCsn (Class.cv (nb072AlphaDummy049 x H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0007 x H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072AlphaDummy047 x H)
          (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
        (synCsn (Class.cv (nb072AlphaDummy049 x H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072AlphaDummy047 x H)
        (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0005 x H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0010 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy050 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072AlphaDummy048 A B R S_cls H) (Wff.classEq
              (Class.cab (nb072AlphaDummy046 A B R S_cls H)
                (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
                  (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
              (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb072AlphaDummy048 A B R S_cls H)
      (Wff.classEq (Class.cab (nb072AlphaDummy046 A B R S_cls H)
          (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
        (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0006 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072AlphaDummy046 A B R S_cls H)
          (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
            (Class.cv (nb072AlphaDummy046 A B R S_cls H))))
        (synCsn (Class.cv (nb072AlphaDummy048 A B R S_cls H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072AlphaDummy046 A B R S_cls H)
        (synWbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
          (Class.cv (nb072AlphaDummy046 A B R S_cls H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0004 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv (nb072AlphaDummy000 A B R S_cls H)) H
          (Class.cv (nb072AlphaDummy046 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0011 (x : Var) (H : Class) :
    (nb072AlphaDummy052 x H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072AlphaDummy049 x H) (Wff.classEq
              (Class.cab (nb072AlphaDummy047 x H)
                (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
              (synCsn (Class.cv (nb072AlphaDummy049 x H)))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb072AlphaDummy049 x H)
      (Wff.classEq (Class.cab (nb072AlphaDummy047 x H)
          (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
        (synCsn (Class.cv (nb072AlphaDummy049 x H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0007 x H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072AlphaDummy047 x H)
          (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))))
        (synCsn (Class.cv (nb072AlphaDummy049 x H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072AlphaDummy047 x H)
        (synWbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0005 x H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv x) H (Class.cv (nb072AlphaDummy047 x H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0012 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy039 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
          ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0013 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy041 x y H) ∉ H.fv :=
  by
  change freshVar (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) 1 ∉ H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv x)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0014 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy038 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))).fv ∪
          ((synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0015 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy040 x y H) ∉ H.fv :=
  by
  change freshVar (((synCfv H (Class.cv x))).fv ∪ ((synCfv H (Class.cv y))).fv) 0 ∉ H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv x)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0016 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy044 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv ∪
          ((Class.cab (nb072AlphaDummy038 A B R S_cls H)
              (synWrex (nb072AlphaDummy039 A B R S_cls H)
                (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                  (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb072AlphaDummy038 A B R S_cls H)
      (synWrex (nb072AlphaDummy039 A B R S_cls H)
        (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
          (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0014 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072AlphaDummy039 A B R S_cls H)
        (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
          (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0012 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0017 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy045 x y H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv ∪
          ((Class.cab (nb072AlphaDummy040 x y H)
              (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                  (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb072AlphaDummy040 x y H)
      (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
          (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0015 x y H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
          (synCphi (Class.cv (nb072AlphaDummy041 x y H))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0013 x y H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv x)]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0018 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy042 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
                (synWrex (nb072AlphaDummy039 A B R S_cls H)
                  (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
                  (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                    (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))))).fv ∪
          ((synCcompl (Class.cab (nb072AlphaDummy038 A B R S_cls H)
                (synWrex (nb072AlphaDummy039 A B R S_cls H)
                  (synCfv H (Class.cv (nb072AlphaDummy001 A B R S_cls H)))
                  (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
                    (synCun (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb072AlphaDummy038 A B R S_cls H)
        (synWrex (nb072AlphaDummy039 A B R S_cls H)
          (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
          (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
            (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))))]
  rw [fv_class_cab (nb072AlphaDummy038 A B R S_cls H)
      (synWrex (nb072AlphaDummy039 A B R S_cls H)
        (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
          (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0014 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072AlphaDummy039 A B R S_cls H)
        (synCfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072AlphaDummy038 A B R S_cls H))
          (synCphi (Class.cv (nb072AlphaDummy039 A B R S_cls H))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0012 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv (nb072AlphaDummy000 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0019 (x : Var) (y : Var) (H : Class) :
    (nb072AlphaDummy043 x y H) ∉ H.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb072AlphaDummy040 x y H)
                (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
                  (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                    (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))))).fv ∪ ((synCcompl
              (Class.cab (nb072AlphaDummy040 x y H)
                (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv y))
                  (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
                    (synCun (synCphi (Class.cv (nb072AlphaDummy041 x y H)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb072AlphaDummy040 x y H)
        (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
          (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
            (synCphi (Class.cv (nb072AlphaDummy041 x y H))))))]
  rw [fv_class_cab (nb072AlphaDummy040 x y H)
      (synWrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
          (synCphi (Class.cv (nb072AlphaDummy041 x y H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0015 x y H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072AlphaDummy041 x y H) (synCfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072AlphaDummy040 x y H))
          (synCphi (Class.cv (nb072AlphaDummy041 x y H))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0013 x y H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv x)]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0020 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy001 A B R S_cls H) ∉ H.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))))

theorem nb072_focused_notmem_0021 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072AlphaDummy000 A B R S_cls H) ∉ H.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part011`. -/


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

theorem nb072_compact_envfresh_0018 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) :
    TEnvFresh
      [((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      H.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072AlphaDummy046 A B R S_cls H) (nb072AlphaDummy047 x H)
      (nb072_focused_notmem_0004 A B R S_cls H) (nb072_focused_notmem_0005 x H)
      (TEnvFresh.consFresh (nb072AlphaDummy048 A B R S_cls H)
        (nb072AlphaDummy049 x H) (nb072_focused_notmem_0006 A B R S_cls H)
        (nb072_focused_notmem_0007 x H)
        (TEnvFresh.consFresh (nb072AlphaDummy051 A B R S_cls H)
          (nb072AlphaDummy053 x H) (nb072_focused_notmem_0008 A B R S_cls H)
          (nb072_focused_notmem_0009 x H)
          (TEnvFresh.consFresh (nb072AlphaDummy050 A B R S_cls H)
            (nb072AlphaDummy052 x H) (nb072_focused_notmem_0010 A B R S_cls H)
            (nb072_focused_notmem_0011 x H)
            (TEnvFresh.consFresh (nb072AlphaDummy039 A B R S_cls H)
              (nb072AlphaDummy041 x y H) (nb072_focused_notmem_0012 A B R S_cls H)
              (nb072_focused_notmem_0013 x y H)
              (TEnvFresh.consFresh (nb072AlphaDummy038 A B R S_cls H)
                (nb072AlphaDummy040 x y H) (nb072_focused_notmem_0014 A B R S_cls H)
                (nb072_focused_notmem_0015 x y H)
                (TEnvFresh.consFresh (nb072AlphaDummy044 A B R S_cls H)
                  (nb072AlphaDummy045 x y H) (nb072_focused_notmem_0016 A B R S_cls H)
                  (nb072_focused_notmem_0017 x y H)
                  (TEnvFresh.consFresh (nb072AlphaDummy042 A B R S_cls H)
                    (nb072AlphaDummy043 x y H) (nb072_focused_notmem_0018 A B R S_cls H)
                    (nb072_focused_notmem_0019 x y H)
                    (TEnvFresh.consFresh (nb072AlphaDummy001 A B R S_cls H) y
                      (nb072_focused_notmem_0020 A B R S_cls H) dv_H_y
                      (TEnvFresh.consFresh (nb072AlphaDummy000 A B R S_cls H) x
                        (nb072_focused_notmem_0021 A B R S_cls H) dv_H_x
                        (TEnvFresh.nil H.fv)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb072_focused_refl_0003`. -/
@[expose]
noncomputable def nb072FocusedRefl0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) :
    TReflOn
      [((nb072AlphaDummy046 A B R S_cls H), (nb072AlphaDummy047 x H)),
        ((nb072AlphaDummy048 A B R S_cls H), (nb072AlphaDummy049 x H)),
        ((nb072AlphaDummy051 A B R S_cls H), (nb072AlphaDummy053 x H)),
        ((nb072AlphaDummy050 A B R S_cls H), (nb072AlphaDummy052 x H)),
        ((nb072AlphaDummy039 A B R S_cls H), (nb072AlphaDummy041 x y H)),
        ((nb072AlphaDummy038 A B R S_cls H), (nb072AlphaDummy040 x y H)),
        ((nb072AlphaDummy044 A B R S_cls H), (nb072AlphaDummy045 x y H)),
        ((nb072AlphaDummy042 A B R S_cls H), (nb072AlphaDummy043 x y H)),
        ((nb072AlphaDummy001 A B R S_cls H), y),
        ((nb072AlphaDummy000 A B R S_cls H), x)]
      H.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0018 x y A B R S_cls H dv_H_x dv_H_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
