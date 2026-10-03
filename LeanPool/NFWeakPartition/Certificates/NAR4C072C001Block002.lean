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

@[expose]
noncomputable def nb072_split_alpha_0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_060 A B R S_cls H))
          (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_060 A B R S_cls H))
            (Class.cab (nb072_alpha_dummy_054 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_055 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_054 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_061 x H))
          (Class.cab (nb072_alpha_dummy_056 x H)
            (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_061 x H))
            (Class.cab (nb072_alpha_dummy_056 x H)
              (syn_wrex (nb072_alpha_dummy_057 x H) (Class.cv x)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_056 x H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                      (nb072_alpha_dummy_055 A B R S_cls H) from (by
                      unfold nb072_alpha_dummy_055;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H) 1))))
                  (show x ≠ (nb072_alpha_dummy_057 x H) from (by
                      unfold nb072_alpha_dummy_057;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0052 x H) 1)))) (TAlphaVar.there
                    (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                        (nb072_alpha_dummy_054 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_054;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H)
                                0)))) (show x ≠ (nb072_alpha_dummy_056 x H) from (by
                        unfold nb072_alpha_dummy_056;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                          (nb072_alpha_dummy_060 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_060;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0054 A B R S_cls H)
                                  0)))) (show x ≠ (nb072_alpha_dummy_061 x H) from (by
                          unfold nb072_alpha_dummy_061;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0055 x H) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                            (nb072_alpha_dummy_058 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0051 A B R S_cls H)
                                    0)))) (show x ≠ (nb072_alpha_dummy_059 x H) from (by
                            unfold nb072_alpha_dummy_059;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0053 x H) 0))))
                        (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                              (nb072_alpha_dummy_046 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0044 A B R S_cls H) 0))))
                          (show x ≠ (nb072_alpha_dummy_047 x H) from (by
                              unfold nb072_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0047 x H) 0))))
                          (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                (nb072_alpha_dummy_048 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_048;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0045 A B R S_cls H) 0))))
                            (show x ≠ (nb072_alpha_dummy_049 x H) from (by
                                unfold nb072_alpha_dummy_049;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0048 x H) 0))))
                            (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_051 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0046 A B R S_cls H) 1))))
                              (show x ≠ (nb072_alpha_dummy_053 x H) from (by
                                  unfold nb072_alpha_dummy_053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                          1)))) (TAlphaVar.there (show
                                  (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                    (nb072_alpha_dummy_050 A B R S_cls H) from (by
                                    unfold nb072_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0046 A B R S_cls H) 0))))
                                (show x ≠ (nb072_alpha_dummy_052 x H) from (by
                                    unfold nb072_alpha_dummy_052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                            0)))) (TAlphaVar.there (show
                                    (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_039 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_039;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0038 A B R S_cls H) 1))))
                                  (show x ≠ (nb072_alpha_dummy_041 x y H) from (by
                                      unfold nb072_alpha_dummy_041;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0040 x y H) 1))))
                                  (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_038 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_038;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0038 A B R S_cls H)
                                                0))))
                                    (show x ≠ (nb072_alpha_dummy_040 x y H) from (by
                                        unfold nb072_alpha_dummy_040;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0040 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_000 A B R S_cls H) ≠
        (nb072_alpha_dummy_044 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_044;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0042 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072_alpha_dummy_045 x y H) from (by
                                          unfold nb072_alpha_dummy_045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0043 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_042 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0039 A B R S_cls H)
                  0)))) (show x ≠ (nb072_alpha_dummy_043 x y H) from (by
          unfold nb072_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0041 x y H) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
                      ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb072_alpha_dummy_055 A B R S_cls H) ≠
                              (nb072_alpha_dummy_062 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0056 A B R S_cls H) 0))))
                          (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_064 x H) from
                            (by
                              unfold nb072_alpha_dummy_064;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0057 x H) 0))))
                          (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                                (nb072_alpha_dummy_063 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_063;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0056 A B R S_cls H) 1)))) (show
                              (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_065 x H) from (by
                                unfold nb072_alpha_dummy_065;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0057 x H) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb072_alpha_dummy_057 x H))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_069 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_072 x H) from (by
          unfold nb072_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H) 1)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_062 A B R S_cls H) ≠ (nb072_alpha_dummy_068 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_071 x H) from (by
          unfold nb072_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_066 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from (by
          unfold nb072_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)),
        ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)),
        ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)),
        ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)),
        ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)),
        ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)),
        ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)),
        ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)),
        ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)),
        ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)),
        ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R
        S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_080
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_080
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_070
        A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_070
        A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0058 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_064 x H) ≠
                                        (nb072_alpha_dummy_067 x H) from (by
                                        unfold nb072_alpha_dummy_067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0059 x H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb072_alpha_dummy_066 A B R S_cls H),
                                      (nb072_alpha_dummy_067 x H)),
                                    ((nb072_alpha_dummy_062 A B R S_cls H),
                                      (nb072_alpha_dummy_064 x H)),
                                    ((nb072_alpha_dummy_063 A B R S_cls H),
                                      (nb072_alpha_dummy_065 x H)),
                                    ((nb072_alpha_dummy_055 A B R S_cls H),
                                      (nb072_alpha_dummy_057 x H)),
                                    ((nb072_alpha_dummy_054 A B R S_cls H),
                                      (nb072_alpha_dummy_056 x H)),
                                    ((nb072_alpha_dummy_060 A B R S_cls H),
                                      (nb072_alpha_dummy_061 x H)),
                                    ((nb072_alpha_dummy_058 A B R S_cls H),
                                      (nb072_alpha_dummy_059 x H)),
                                    ((nb072_alpha_dummy_046 A B R S_cls H),
                                      (nb072_alpha_dummy_047 x H)),
                                    ((nb072_alpha_dummy_048 A B R S_cls H),
                                      (nb072_alpha_dummy_049 x H)),
                                    ((nb072_alpha_dummy_051 A B R S_cls H),
                                      (nb072_alpha_dummy_053 x H)),
                                    ((nb072_alpha_dummy_050 A B R S_cls H),
                                      (nb072_alpha_dummy_052 x H)),
                                    ((nb072_alpha_dummy_039 A B R S_cls H),
                                      (nb072_alpha_dummy_041 x y H)),
                                    ((nb072_alpha_dummy_038 A B R S_cls H),
                                      (nb072_alpha_dummy_040 x y H)),
                                    ((nb072_alpha_dummy_044 A B R S_cls H),
                                      (nb072_alpha_dummy_045 x y H)),
                                    ((nb072_alpha_dummy_042 A B R S_cls H),
                                      (nb072_alpha_dummy_043 x y H)),
                                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                    ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_066;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                                    (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H)
                                    from (by
                                      unfold nb072_alpha_dummy_067;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0059 x H)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0058 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_064 x H) ≠
                                        (nb072_alpha_dummy_067 x H) from (by
                                        unfold nb072_alpha_dummy_067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0059 x H) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb072_alpha_dummy_066 A B R S_cls H),
                                      (nb072_alpha_dummy_067 x H)),
                                    ((nb072_alpha_dummy_062 A B R S_cls H),
                                      (nb072_alpha_dummy_064 x H)),
                                    ((nb072_alpha_dummy_063 A B R S_cls H),
                                      (nb072_alpha_dummy_065 x H)),
                                    ((nb072_alpha_dummy_055 A B R S_cls H),
                                      (nb072_alpha_dummy_057 x H)),
                                    ((nb072_alpha_dummy_054 A B R S_cls H),
                                      (nb072_alpha_dummy_056 x H)),
                                    ((nb072_alpha_dummy_060 A B R S_cls H),
                                      (nb072_alpha_dummy_061 x H)),
                                    ((nb072_alpha_dummy_058 A B R S_cls H),
                                      (nb072_alpha_dummy_059 x H)),
                                    ((nb072_alpha_dummy_046 A B R S_cls H),
                                      (nb072_alpha_dummy_047 x H)),
                                    ((nb072_alpha_dummy_048 A B R S_cls H),
                                      (nb072_alpha_dummy_049 x H)),
                                    ((nb072_alpha_dummy_051 A B R S_cls H),
                                      (nb072_alpha_dummy_053 x H)),
                                    ((nb072_alpha_dummy_050 A B R S_cls H),
                                      (nb072_alpha_dummy_052 x H)),
                                    ((nb072_alpha_dummy_039 A B R S_cls H),
                                      (nb072_alpha_dummy_041 x y H)),
                                    ((nb072_alpha_dummy_038 A B R S_cls H),
                                      (nb072_alpha_dummy_040 x y H)),
                                    ((nb072_alpha_dummy_044 A B R S_cls H),
                                      (nb072_alpha_dummy_045 x y H)),
                                    ((nb072_alpha_dummy_042 A B R S_cls H),
                                      (nb072_alpha_dummy_043 x y H)),
                                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                    ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                        (nb072_alpha_dummy_055 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_055;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H)
                                1)))) (show x ≠ (nb072_alpha_dummy_057 x H) from (by
                        unfold nb072_alpha_dummy_057;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0052 x H) 1))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                          (nb072_alpha_dummy_054 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0050 A B R S_cls H)
                                  0)))) (show x ≠ (nb072_alpha_dummy_056 x H) from (by
                          unfold nb072_alpha_dummy_056;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0052 x H) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                            (nb072_alpha_dummy_060 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_060;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0054 A B R S_cls H)
                                    0)))) (show x ≠ (nb072_alpha_dummy_061 x H) from (by
                            unfold nb072_alpha_dummy_061;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0055 x H) 0))))
                        (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                              (nb072_alpha_dummy_058 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_058;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0051 A B R S_cls H) 0))))
                          (show x ≠ (nb072_alpha_dummy_059 x H) from (by
                              unfold nb072_alpha_dummy_059;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0053 x H) 0))))
                          (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                (nb072_alpha_dummy_046 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_046;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0044 A B R S_cls H) 0))))
                            (show x ≠ (nb072_alpha_dummy_047 x H) from (by
                                unfold nb072_alpha_dummy_047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0047 x H) 0))))
                            (TAlphaVar.there (show (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_048 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0045 A B R S_cls H) 0))))
                              (show x ≠ (nb072_alpha_dummy_049 x H) from (by
                                  unfold nb072_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0048 x H)
                                          0)))) (TAlphaVar.there (show
                                  (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                    (nb072_alpha_dummy_051 A B R S_cls H) from (by
                                    unfold nb072_alpha_dummy_051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb072_support_mem_0046 A B R S_cls H) 1))))
                                (show x ≠ (nb072_alpha_dummy_053 x H) from (by
                                    unfold nb072_alpha_dummy_053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                            1)))) (TAlphaVar.there (show
                                    (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_050 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0046 A B R S_cls H) 0))))
                                  (show x ≠ (nb072_alpha_dummy_052 x H) from (by
                                      unfold nb072_alpha_dummy_052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0049 x H)
                                              0)))) (TAlphaVar.there (show
                                      (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_039 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_039;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0038 A B R S_cls H)
                                                1))))
                                    (show x ≠ (nb072_alpha_dummy_041 x y H) from (by
                                        unfold nb072_alpha_dummy_041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0040 x y H) 1))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_000 A B R S_cls H) ≠
        (nb072_alpha_dummy_038 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_038;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0038 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072_alpha_dummy_040 x y H) from (by
                                          unfold nb072_alpha_dummy_040;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0040 x y H) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_044 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0042 A B R S_cls H)
                  0)))) (show x ≠ (nb072_alpha_dummy_045 x y H) from (by
          unfold nb072_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0043 x y H) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_042 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0039 A B R S_cls
                    H)
                  0)))) (show x ≠ (nb072_alpha_dummy_043 x y H) from (by
          unfold nb072_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0041 x y H) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
                        ((Class.cv (nb072_alpha_dummy_046 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv x)).fv ∪ ((Class.cv (nb072_alpha_dummy_047 x H))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_055 A B R S_cls H) ≠
                                (nb072_alpha_dummy_062 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_062;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0056 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_064 x H) from (by
                                unfold nb072_alpha_dummy_064;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0057 x H) 0))))
                            (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_063 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_063;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0056 A B R S_cls H) 1)))) (show
                                (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_065 x H) from
                                (by
                                  unfold nb072_alpha_dummy_065;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0057 x H)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb072_alpha_dummy_057 x H))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_062 A B R S_cls H) ≠ (nb072_alpha_dummy_069 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_072 x H) from (by
          unfold nb072_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_068 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_071 x H) from (by
          unfold nb072_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_066 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B
                    R S_cls H)
                  0)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from (by
          unfold nb072_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)),
        ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)),
        ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)),
        ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)),
        ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)),
        ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_076
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)),
        ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)),
        ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)),
        ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)),
        ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)),
        ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_060 A B R S_cls H), (nb072_alpha_dummy_061 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R
        S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_064 x
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_080
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_080
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_070
        A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_070
        A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0058 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_064 x H) ≠
        (nb072_alpha_dummy_067 x H) from (by
                                          unfold nb072_alpha_dummy_067;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0059 x H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb072_alpha_dummy_066 A B R S_cls H),
                                        (nb072_alpha_dummy_067 x H)),
                                      ((nb072_alpha_dummy_062 A B R S_cls H),
                                        (nb072_alpha_dummy_064 x H)),
                                      ((nb072_alpha_dummy_063 A B R S_cls H),
                                        (nb072_alpha_dummy_065 x H)),
                                      ((nb072_alpha_dummy_055 A B R S_cls H),
                                        (nb072_alpha_dummy_057 x H)),
                                      ((nb072_alpha_dummy_054 A B R S_cls H),
                                        (nb072_alpha_dummy_056 x H)),
                                      ((nb072_alpha_dummy_060 A B R S_cls H),
                                        (nb072_alpha_dummy_061 x H)),
                                      ((nb072_alpha_dummy_058 A B R S_cls H),
                                        (nb072_alpha_dummy_059 x H)),
                                      ((nb072_alpha_dummy_046 A B R S_cls H),
                                        (nb072_alpha_dummy_047 x H)),
                                      ((nb072_alpha_dummy_048 A B R S_cls H),
                                        (nb072_alpha_dummy_049 x H)),
                                      ((nb072_alpha_dummy_051 A B R S_cls H),
                                        (nb072_alpha_dummy_053 x H)),
                                      ((nb072_alpha_dummy_050 A B R S_cls H),
                                        (nb072_alpha_dummy_052 x H)),
                                      ((nb072_alpha_dummy_039 A B R S_cls H),
                                        (nb072_alpha_dummy_041 x y H)),
                                      ((nb072_alpha_dummy_038 A B R S_cls H),
                                        (nb072_alpha_dummy_040 x y H)),
                                      ((nb072_alpha_dummy_044 A B R S_cls H),
                                        (nb072_alpha_dummy_045 x y H)),
                                      ((nb072_alpha_dummy_042 A B R S_cls H),
                                        (nb072_alpha_dummy_043 x y H)),
                                      ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                      ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_066;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0058 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_064 x H) ≠
                                        (nb072_alpha_dummy_067 x H) from (by
                                        unfold nb072_alpha_dummy_067;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0059 x H) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_066;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0058 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_064 x H) ≠
        (nb072_alpha_dummy_067 x H) from (by
                                          unfold nb072_alpha_dummy_067;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0059 x H) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb072_alpha_dummy_066 A B R S_cls H),
                                        (nb072_alpha_dummy_067 x H)),
                                      ((nb072_alpha_dummy_062 A B R S_cls H),
                                        (nb072_alpha_dummy_064 x H)),
                                      ((nb072_alpha_dummy_063 A B R S_cls H),
                                        (nb072_alpha_dummy_065 x H)),
                                      ((nb072_alpha_dummy_055 A B R S_cls H),
                                        (nb072_alpha_dummy_057 x H)),
                                      ((nb072_alpha_dummy_054 A B R S_cls H),
                                        (nb072_alpha_dummy_056 x H)),
                                      ((nb072_alpha_dummy_060 A B R S_cls H),
                                        (nb072_alpha_dummy_061 x H)),
                                      ((nb072_alpha_dummy_058 A B R S_cls H),
                                        (nb072_alpha_dummy_059 x H)),
                                      ((nb072_alpha_dummy_046 A B R S_cls H),
                                        (nb072_alpha_dummy_047 x H)),
                                      ((nb072_alpha_dummy_048 A B R S_cls H),
                                        (nb072_alpha_dummy_049 x H)),
                                      ((nb072_alpha_dummy_051 A B R S_cls H),
                                        (nb072_alpha_dummy_053 x H)),
                                      ((nb072_alpha_dummy_050 A B R S_cls H),
                                        (nb072_alpha_dummy_052 x H)),
                                      ((nb072_alpha_dummy_039 A B R S_cls H),
                                        (nb072_alpha_dummy_041 x y H)),
                                      ((nb072_alpha_dummy_038 A B R S_cls H),
                                        (nb072_alpha_dummy_040 x y H)),
                                      ((nb072_alpha_dummy_044 A B R S_cls H),
                                        (nb072_alpha_dummy_045 x y H)),
                                      ((nb072_alpha_dummy_042 A B R S_cls H),
                                        (nb072_alpha_dummy_043 x y H)),
                                      ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                      ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_cnnc)
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

@[expose]
noncomputable def nb072_split_alpha_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) :
    TAlphaWff
      [((nb072_alpha_dummy_088 A B R S_cls H), (nb072_alpha_dummy_089 x H)),
        ((nb072_alpha_dummy_086 A B R S_cls H), (nb072_alpha_dummy_087 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_084 A B R S_cls H), (nb072_alpha_dummy_085 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_088 A B R S_cls H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H)))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_088 A B R S_cls H))
            (syn_cphi (Class.cv (nb072_alpha_dummy_055 A B R S_cls H))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_089 x H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_089 x H))
            (syn_cphi (Class.cv (nb072_alpha_dummy_057 x H)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                      (nb072_alpha_dummy_062 A B R S_cls H) from (by
                      unfold nb072_alpha_dummy_062;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H) 0))))
                  (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_064 x H) from (by
                      unfold nb072_alpha_dummy_064;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0057 x H) 0)))) (TAlphaVar.there
                    (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                        (nb072_alpha_dummy_063 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_063;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H)
                                1))))
                    (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_065 x H) from (by
                        unfold nb072_alpha_dummy_065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0057 x H) 1))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                          (nb072_alpha_dummy_088 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_088;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0086 A B R S_cls H)
                                  0))))
                      (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_089 x H) from (by
                          unfold nb072_alpha_dummy_089;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0087 x H) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                            (nb072_alpha_dummy_086 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_086;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0084 A B R S_cls H)
                                    0))))
                        (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_087 x H) from (by
                            unfold nb072_alpha_dummy_087;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0085 x H) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb072_alpha_dummy_057 x H))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_069 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_069;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0060 A B R S_cls H)
                                                1)))) (show (nb072_alpha_dummy_064 x H) ≠
                                        (nb072_alpha_dummy_072 x H) from (by
                                        unfold nb072_alpha_dummy_072;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0061 x H) 1))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_068 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_068;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0060 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_064 x H) ≠
        (nb072_alpha_dummy_071 x H) from (by
                                          unfold nb072_alpha_dummy_071;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0061 x H) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_062 A B R S_cls H) ≠ (nb072_alpha_dummy_066 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from (by
          unfold nb072_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb072_alpha_dummy_070 A B R S_cls H),
        (nb072_alpha_dummy_073 x H)), ((nb072_alpha_dummy_069 A B R S_cls H),
        (nb072_alpha_dummy_072 x H)), ((nb072_alpha_dummy_068 A B R S_cls H),
        (nb072_alpha_dummy_071 x H)), ((nb072_alpha_dummy_066 A B R S_cls H),
        (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H),
        (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H),
        (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_088 A B R S_cls H),
        (nb072_alpha_dummy_089 x H)), ((nb072_alpha_dummy_086 A B R S_cls H),
        (nb072_alpha_dummy_087 x H)), ((nb072_alpha_dummy_055 A B R S_cls H),
        (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H),
        (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_084 A B R S_cls H),
        (nb072_alpha_dummy_085 x H)), ((nb072_alpha_dummy_058 A B R S_cls H),
        (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H),
        (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H),
        (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H),
        (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H),
        (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H),
        (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H),
        (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H),
        (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H),
        (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb072_alpha_dummy_070 A B R S_cls H),
        (nb072_alpha_dummy_073 x H)), ((nb072_alpha_dummy_069 A B R S_cls H),
        (nb072_alpha_dummy_072 x H)), ((nb072_alpha_dummy_068 A B R S_cls H),
        (nb072_alpha_dummy_071 x H)), ((nb072_alpha_dummy_066 A B R S_cls H),
        (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H),
        (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H),
        (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_088 A B R S_cls H),
        (nb072_alpha_dummy_089 x H)), ((nb072_alpha_dummy_086 A B R S_cls H),
        (nb072_alpha_dummy_087 x H)), ((nb072_alpha_dummy_055 A B R S_cls H),
        (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H),
        (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_084 A B R S_cls H),
        (nb072_alpha_dummy_085 x H)), ((nb072_alpha_dummy_058 A B R S_cls H),
        (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H),
        (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H),
        (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H),
        (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H),
        (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H),
        (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H),
        (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H),
        (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H),
        (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_c0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_080 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_080 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from (by
                                unfold nb072_alpha_dummy_067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)),
                            ((nb072_alpha_dummy_062 A B R S_cls H),
                              (nb072_alpha_dummy_064 x H)),
                            ((nb072_alpha_dummy_063 A B R S_cls H),
                              (nb072_alpha_dummy_065 x H)),
                            ((nb072_alpha_dummy_088 A B R S_cls H),
                              (nb072_alpha_dummy_089 x H)),
                            ((nb072_alpha_dummy_086 A B R S_cls H),
                              (nb072_alpha_dummy_087 x H)),
                            ((nb072_alpha_dummy_055 A B R S_cls H),
                              (nb072_alpha_dummy_057 x H)),
                            ((nb072_alpha_dummy_054 A B R S_cls H),
                              (nb072_alpha_dummy_056 x H)),
                            ((nb072_alpha_dummy_084 A B R S_cls H),
                              (nb072_alpha_dummy_085 x H)),
                            ((nb072_alpha_dummy_058 A B R S_cls H),
                              (nb072_alpha_dummy_059 x H)),
                            ((nb072_alpha_dummy_046 A B R S_cls H),
                              (nb072_alpha_dummy_047 x H)),
                            ((nb072_alpha_dummy_048 A B R S_cls H),
                              (nb072_alpha_dummy_049 x H)),
                            ((nb072_alpha_dummy_051 A B R S_cls H),
                              (nb072_alpha_dummy_053 x H)),
                            ((nb072_alpha_dummy_050 A B R S_cls H),
                              (nb072_alpha_dummy_052 x H)),
                            ((nb072_alpha_dummy_039 A B R S_cls H),
                              (nb072_alpha_dummy_041 x y H)),
                            ((nb072_alpha_dummy_038 A B R S_cls H),
                              (nb072_alpha_dummy_040 x y H)),
                            ((nb072_alpha_dummy_044 A B R S_cls H),
                              (nb072_alpha_dummy_045 x y H)),
                            ((nb072_alpha_dummy_042 A B R S_cls H),
                              (nb072_alpha_dummy_043 x y H)),
                            ((nb072_alpha_dummy_001 A B R S_cls H), y),
                            ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb072_alpha_dummy_062 A B R S_cls H) ≠
                              (nb072_alpha_dummy_066 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_066;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0058 A B R S_cls H) 0))))
                          (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from
                            (by
                              unfold nb072_alpha_dummy_067;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from (by
                                unfold nb072_alpha_dummy_067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)),
                            ((nb072_alpha_dummy_062 A B R S_cls H),
                              (nb072_alpha_dummy_064 x H)),
                            ((nb072_alpha_dummy_063 A B R S_cls H),
                              (nb072_alpha_dummy_065 x H)),
                            ((nb072_alpha_dummy_088 A B R S_cls H),
                              (nb072_alpha_dummy_089 x H)),
                            ((nb072_alpha_dummy_086 A B R S_cls H),
                              (nb072_alpha_dummy_087 x H)),
                            ((nb072_alpha_dummy_055 A B R S_cls H),
                              (nb072_alpha_dummy_057 x H)),
                            ((nb072_alpha_dummy_054 A B R S_cls H),
                              (nb072_alpha_dummy_056 x H)),
                            ((nb072_alpha_dummy_084 A B R S_cls H),
                              (nb072_alpha_dummy_085 x H)),
                            ((nb072_alpha_dummy_058 A B R S_cls H),
                              (nb072_alpha_dummy_059 x H)),
                            ((nb072_alpha_dummy_046 A B R S_cls H),
                              (nb072_alpha_dummy_047 x H)),
                            ((nb072_alpha_dummy_048 A B R S_cls H),
                              (nb072_alpha_dummy_049 x H)),
                            ((nb072_alpha_dummy_051 A B R S_cls H),
                              (nb072_alpha_dummy_053 x H)),
                            ((nb072_alpha_dummy_050 A B R S_cls H),
                              (nb072_alpha_dummy_052 x H)),
                            ((nb072_alpha_dummy_039 A B R S_cls H),
                              (nb072_alpha_dummy_041 x y H)),
                            ((nb072_alpha_dummy_038 A B R S_cls H),
                              (nb072_alpha_dummy_040 x y H)),
                            ((nb072_alpha_dummy_044 A B R S_cls H),
                              (nb072_alpha_dummy_045 x y H)),
                            ((nb072_alpha_dummy_042 A B R S_cls H),
                              (nb072_alpha_dummy_043 x y H)),
                            ((nb072_alpha_dummy_001 A B R S_cls H), y),
                            ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                        (nb072_alpha_dummy_062 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_062;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H)
                                0))))
                    (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_064 x H) from (by
                        unfold nb072_alpha_dummy_064;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0057 x H) 0))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                          (nb072_alpha_dummy_063 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0056 A B R S_cls H)
                                  1))))
                      (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_065 x H) from (by
                          unfold nb072_alpha_dummy_065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0057 x H) 1))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                            (nb072_alpha_dummy_088 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_088;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0086 A B R S_cls H)
                                    0))))
                        (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_089 x H) from (by
                            unfold nb072_alpha_dummy_089;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0087 x H) 0))))
                        (TAlphaVar.there (show (nb072_alpha_dummy_055 A B R S_cls H) ≠
                              (nb072_alpha_dummy_086 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_086;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0084 A B R S_cls H) 0))))
                          (show (nb072_alpha_dummy_057 x H) ≠ (nb072_alpha_dummy_087 x H) from
                            (by
                              unfold nb072_alpha_dummy_087;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0085 x H) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072_alpha_dummy_055 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb072_alpha_dummy_057 x H))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_062 A B R S_cls H) ≠
        (nb072_alpha_dummy_069 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0060 A B R S_cls H)
                                                  1)))) (show (nb072_alpha_dummy_064 x H) ≠
        (nb072_alpha_dummy_072 x H) from (by
                                          unfold nb072_alpha_dummy_072;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0061 x H) 1))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_062 A B R S_cls H) ≠ (nb072_alpha_dummy_068 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0060 A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_071 x H) from (by
          unfold nb072_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0061 x H) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_062 A B R S_cls H) ≠ (nb072_alpha_dummy_066 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0058 A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from (by
          unfold nb072_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0059 x H) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb072_alpha_dummy_070 A B R S_cls H),
        (nb072_alpha_dummy_073 x H)), ((nb072_alpha_dummy_069 A B R S_cls H),
        (nb072_alpha_dummy_072 x H)), ((nb072_alpha_dummy_068 A B R S_cls H),
        (nb072_alpha_dummy_071 x H)), ((nb072_alpha_dummy_066 A B R S_cls H),
        (nb072_alpha_dummy_067 x H)), ((nb072_alpha_dummy_062 A B R S_cls H),
        (nb072_alpha_dummy_064 x H)), ((nb072_alpha_dummy_063 A B R S_cls H),
        (nb072_alpha_dummy_065 x H)), ((nb072_alpha_dummy_088 A B R S_cls H),
        (nb072_alpha_dummy_089 x H)), ((nb072_alpha_dummy_086 A B R S_cls H),
        (nb072_alpha_dummy_087 x H)), ((nb072_alpha_dummy_055 A B R S_cls H),
        (nb072_alpha_dummy_057 x H)), ((nb072_alpha_dummy_054 A B R S_cls H),
        (nb072_alpha_dummy_056 x H)), ((nb072_alpha_dummy_084 A B R S_cls H),
        (nb072_alpha_dummy_085 x H)), ((nb072_alpha_dummy_058 A B R S_cls H),
        (nb072_alpha_dummy_059 x H)), ((nb072_alpha_dummy_046 A B R S_cls H),
        (nb072_alpha_dummy_047 x H)), ((nb072_alpha_dummy_048 A B R S_cls H),
        (nb072_alpha_dummy_049 x H)), ((nb072_alpha_dummy_051 A B R S_cls H),
        (nb072_alpha_dummy_053 x H)), ((nb072_alpha_dummy_050 A B R S_cls H),
        (nb072_alpha_dummy_052 x H)), ((nb072_alpha_dummy_039 A B R S_cls H),
        (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H),
        (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_044 A B R S_cls H),
        (nb072_alpha_dummy_045 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H),
        (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0064
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0065
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0062
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0063
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_076 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0068
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_077 x H) from (by
          unfold
            nb072_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0069
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_074 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0066
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_075 x H) from (by
          unfold
            nb072_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0067
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_070 A B R S_cls H), (nb072_alpha_dummy_073 x H)),
        ((nb072_alpha_dummy_069 A B R S_cls H), (nb072_alpha_dummy_072 x H)),
        ((nb072_alpha_dummy_068 A B R S_cls H), (nb072_alpha_dummy_071 x H)),
        ((nb072_alpha_dummy_066 A B R S_cls H), (nb072_alpha_dummy_067 x H)),
        ((nb072_alpha_dummy_062 A B R S_cls H), (nb072_alpha_dummy_064 x H)),
        ((nb072_alpha_dummy_063 A B R S_cls H), (nb072_alpha_dummy_065 x H)),
        ((nb072_alpha_dummy_088 A B R S_cls H), (nb072_alpha_dummy_089 x H)),
        ((nb072_alpha_dummy_086 A B R S_cls H), (nb072_alpha_dummy_087 x H)),
        ((nb072_alpha_dummy_055 A B R S_cls H), (nb072_alpha_dummy_057 x H)),
        ((nb072_alpha_dummy_054 A B R S_cls H), (nb072_alpha_dummy_056 x H)),
        ((nb072_alpha_dummy_084 A B R S_cls H), (nb072_alpha_dummy_085 x H)),
        ((nb072_alpha_dummy_058 A B R S_cls H), (nb072_alpha_dummy_059 x H)),
        ((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_062 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_069 A B R S_cls H) ≠ (nb072_alpha_dummy_080 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_080 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0072
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_081 x H) from (by
          unfold
            nb072_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0073
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_069 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0070
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_072 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0071
                    x H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_062
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_064 x H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_070 A B R S_cls H) ≠ (nb072_alpha_dummy_082 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0076
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_083 x H) from (by
          unfold
            nb072_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0077
                    x H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_070 A B R S_cls H) ≠
        (nb072_alpha_dummy_078 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0074
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_073 x H) ≠ (nb072_alpha_dummy_079 x H) from (by
          unfold
            nb072_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0075
                    x H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                                (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from
                                (by
                                  unfold nb072_alpha_dummy_067;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0059 x H)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb072_alpha_dummy_066 A B R S_cls H),
                                (nb072_alpha_dummy_067 x H)),
                              ((nb072_alpha_dummy_062 A B R S_cls H),
                                (nb072_alpha_dummy_064 x H)),
                              ((nb072_alpha_dummy_063 A B R S_cls H),
                                (nb072_alpha_dummy_065 x H)),
                              ((nb072_alpha_dummy_088 A B R S_cls H),
                                (nb072_alpha_dummy_089 x H)),
                              ((nb072_alpha_dummy_086 A B R S_cls H),
                                (nb072_alpha_dummy_087 x H)),
                              ((nb072_alpha_dummy_055 A B R S_cls H),
                                (nb072_alpha_dummy_057 x H)),
                              ((nb072_alpha_dummy_054 A B R S_cls H),
                                (nb072_alpha_dummy_056 x H)),
                              ((nb072_alpha_dummy_084 A B R S_cls H),
                                (nb072_alpha_dummy_085 x H)),
                              ((nb072_alpha_dummy_058 A B R S_cls H),
                                (nb072_alpha_dummy_059 x H)),
                              ((nb072_alpha_dummy_046 A B R S_cls H),
                                (nb072_alpha_dummy_047 x H)),
                              ((nb072_alpha_dummy_048 A B R S_cls H),
                                (nb072_alpha_dummy_049 x H)),
                              ((nb072_alpha_dummy_051 A B R S_cls H),
                                (nb072_alpha_dummy_053 x H)),
                              ((nb072_alpha_dummy_050 A B R S_cls H),
                                (nb072_alpha_dummy_052 x H)),
                              ((nb072_alpha_dummy_039 A B R S_cls H),
                                (nb072_alpha_dummy_041 x y H)),
                              ((nb072_alpha_dummy_038 A B R S_cls H),
                                (nb072_alpha_dummy_040 x y H)),
                              ((nb072_alpha_dummy_044 A B R S_cls H),
                                (nb072_alpha_dummy_045 x y H)),
                              ((nb072_alpha_dummy_042 A B R S_cls H),
                                (nb072_alpha_dummy_043 x y H)),
                              ((nb072_alpha_dummy_001 A B R S_cls H), y),
                              ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_066;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from (by
                                unfold nb072_alpha_dummy_067;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0059 x H) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb072_alpha_dummy_062 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_066 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_066;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0058 A B R S_cls H) 0)))) (show
                                (nb072_alpha_dummy_064 x H) ≠ (nb072_alpha_dummy_067 x H) from
                                (by
                                  unfold nb072_alpha_dummy_067;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0059 x H)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb072_alpha_dummy_066 A B R S_cls H),
                                (nb072_alpha_dummy_067 x H)),
                              ((nb072_alpha_dummy_062 A B R S_cls H),
                                (nb072_alpha_dummy_064 x H)),
                              ((nb072_alpha_dummy_063 A B R S_cls H),
                                (nb072_alpha_dummy_065 x H)),
                              ((nb072_alpha_dummy_088 A B R S_cls H),
                                (nb072_alpha_dummy_089 x H)),
                              ((nb072_alpha_dummy_086 A B R S_cls H),
                                (nb072_alpha_dummy_087 x H)),
                              ((nb072_alpha_dummy_055 A B R S_cls H),
                                (nb072_alpha_dummy_057 x H)),
                              ((nb072_alpha_dummy_054 A B R S_cls H),
                                (nb072_alpha_dummy_056 x H)),
                              ((nb072_alpha_dummy_084 A B R S_cls H),
                                (nb072_alpha_dummy_085 x H)),
                              ((nb072_alpha_dummy_058 A B R S_cls H),
                                (nb072_alpha_dummy_059 x H)),
                              ((nb072_alpha_dummy_046 A B R S_cls H),
                                (nb072_alpha_dummy_047 x H)),
                              ((nb072_alpha_dummy_048 A B R S_cls H),
                                (nb072_alpha_dummy_049 x H)),
                              ((nb072_alpha_dummy_051 A B R S_cls H),
                                (nb072_alpha_dummy_053 x H)),
                              ((nb072_alpha_dummy_050 A B R S_cls H),
                                (nb072_alpha_dummy_052 x H)),
                              ((nb072_alpha_dummy_039 A B R S_cls H),
                                (nb072_alpha_dummy_041 x y H)),
                              ((nb072_alpha_dummy_038 A B R S_cls H),
                                (nb072_alpha_dummy_040 x y H)),
                              ((nb072_alpha_dummy_044 A B R S_cls H),
                                (nb072_alpha_dummy_045 x y H)),
                              ((nb072_alpha_dummy_042 A B R S_cls H),
                                (nb072_alpha_dummy_043 x y H)),
                              ((nb072_alpha_dummy_001 A B R S_cls H), y),
                              ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb072_focused_notmem_0004 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_046 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv) 0 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb072_focused_notmem_0005 (x : Var) (H : Class) :
    (nb072_alpha_dummy_047 x H) ∉ H.fv :=
  by
  change freshVar ((H).fv ∪ ((Class.cv x)).fv) 0 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb072_focused_notmem_0006 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_048 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (({(nb072_alpha_dummy_046 A B R S_cls H)} : Finset Var) ∪
          ((syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
              (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
      (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0007 (x : Var) (H : Class) :
    (nb072_alpha_dummy_049 x H) ∉ H.fv :=
  by
  change
    freshVar
        (({(nb072_alpha_dummy_047 x H)} : Finset Var) ∪
          ((syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0008 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_051 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
                (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                  (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_048 A B R S_cls H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0006 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_046 A B R S_cls H)
        (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0004 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0009 (x : Var) (H : Class) :
    (nb072_alpha_dummy_053 x H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_047 x H)
                (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_049 x H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H)
          (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_049 x H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0007 x H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_047 x H)
          (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_047 x H)
        (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0005 x H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0010 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_050 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_048 A B R S_cls H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
                (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
                  (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_048 A B R S_cls H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0006 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_046 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_048 A B R S_cls H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_046 A B R S_cls H)
        (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_046 A B R S_cls H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0004 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_046 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0011 (x : Var) (H : Class) :
    (nb072_alpha_dummy_052 x H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_049 x H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_047 x H)
                (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_049 x H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_047 x H)
          (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_049 x H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0007 x H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_047 x H)
          (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_049 x H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_047 x H)
        (syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0005 x H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv x) H (Class.cv (nb072_alpha_dummy_047 x H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0012 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_039 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
          ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0013 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_041 x y H) ∉ H.fv :=
  by
  change freshVar (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 1 ∉ H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv x)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0014 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_038 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
          ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0015 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_040 x y H) ∉ H.fv :=
  by
  change freshVar (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) 0 ∉ H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cfv H (Class.cv x)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0016 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_044 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv ∪
          ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb072_alpha_dummy_038 A B R S_cls H)
      (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
        (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0014 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
        (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0012 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0017 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_045 x y H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv ∪
          ((Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb072_alpha_dummy_040 x y H)
      (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0015 x y H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))]
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
    (H : Class) : (nb072_alpha_dummy_042 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
                (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                  (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
                  (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                    (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))))).fv ∪
          ((syn_ccompl (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
                (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                  (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
                  (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                    (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                      (syn_csn (syn_c0c)))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
        (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
          (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
          (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
            (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))))]
  rw [fv_class_cab (nb072_alpha_dummy_038 A B R S_cls H)
      (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
        (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0014 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
        (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0012 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0019 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_043 x y H) ∉ H.fv :=
  by
  change
    freshVar
        (((syn_ccompl (Class.cab (nb072_alpha_dummy_040 x y H)
                (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
                  (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                    (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))))).fv ∪ ((syn_ccompl
              (Class.cab (nb072_alpha_dummy_040 x y H)
                (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
                  (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                    (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                      (syn_csn (syn_c0c)))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb072_alpha_dummy_040 x y H)
        (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
          (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
            (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))))]
  rw [fv_class_cab (nb072_alpha_dummy_040 x y H)
      (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0015 x y H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv x))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))))]
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
    (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∉ H.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))))

theorem nb072_focused_notmem_0021 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∉ H.fv :=
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
      [((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      H.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072_alpha_dummy_046 A B R S_cls H) (nb072_alpha_dummy_047 x H)
      (nb072_focused_notmem_0004 A B R S_cls H) (nb072_focused_notmem_0005 x H)
      (TEnvFresh.consFresh (nb072_alpha_dummy_048 A B R S_cls H)
        (nb072_alpha_dummy_049 x H) (nb072_focused_notmem_0006 A B R S_cls H)
        (nb072_focused_notmem_0007 x H)
        (TEnvFresh.consFresh (nb072_alpha_dummy_051 A B R S_cls H)
          (nb072_alpha_dummy_053 x H) (nb072_focused_notmem_0008 A B R S_cls H)
          (nb072_focused_notmem_0009 x H)
          (TEnvFresh.consFresh (nb072_alpha_dummy_050 A B R S_cls H)
            (nb072_alpha_dummy_052 x H) (nb072_focused_notmem_0010 A B R S_cls H)
            (nb072_focused_notmem_0011 x H)
            (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H)
              (nb072_alpha_dummy_041 x y H) (nb072_focused_notmem_0012 A B R S_cls H)
              (nb072_focused_notmem_0013 x y H)
              (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H)
                (nb072_alpha_dummy_040 x y H) (nb072_focused_notmem_0014 A B R S_cls H)
                (nb072_focused_notmem_0015 x y H)
                (TEnvFresh.consFresh (nb072_alpha_dummy_044 A B R S_cls H)
                  (nb072_alpha_dummy_045 x y H) (nb072_focused_notmem_0016 A B R S_cls H)
                  (nb072_focused_notmem_0017 x y H)
                  (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H)
                    (nb072_alpha_dummy_043 x y H) (nb072_focused_notmem_0018 A B R S_cls H)
                    (nb072_focused_notmem_0019 x y H)
                    (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y
                      (nb072_focused_notmem_0020 A B R S_cls H) dv_H_y
                      (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x
                        (nb072_focused_notmem_0021 A B R S_cls H) dv_H_x
                        (TEnvFresh.nil H.fv)))))))))))

@[expose]
noncomputable def nb072_focused_refl_0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) :
    TReflOn
      [((nb072_alpha_dummy_046 A B R S_cls H), (nb072_alpha_dummy_047 x H)),
        ((nb072_alpha_dummy_048 A B R S_cls H), (nb072_alpha_dummy_049 x H)),
        ((nb072_alpha_dummy_051 A B R S_cls H), (nb072_alpha_dummy_053 x H)),
        ((nb072_alpha_dummy_050 A B R S_cls H), (nb072_alpha_dummy_052 x H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_044 A B R S_cls H), (nb072_alpha_dummy_045 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      H.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0018 x y A B R S_cls H dv_H_x dv_H_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
