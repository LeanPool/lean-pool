/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR5H088P001Part005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR5H088P001Part006`. -/


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
noncomputable def nb088_split_alpha_0003 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) :
    TAlphaWff
      [((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      (Wff.classMem (Class.cv (nb088_alpha_dummy_047 A B C R)) (syn_ccompl
          (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R)
              (syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R))
                (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))))))))
      (Wff.classMem (Class.cv (nb088_alpha_dummy_048 u A B R)) (syn_ccompl
          (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R)
              (syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R))
                (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                          (TAlphaVar.there (show (nb088_alpha_dummy_041 A B C R) ≠
                                (nb088_alpha_dummy_051 A B C R) from (by
                                unfold nb088_alpha_dummy_051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb088_support_mem_0050 A B C R)
                                        0)))) (show (nb088_alpha_dummy_042 u A B R) ≠
                                (nb088_alpha_dummy_052 u A B R) from (by
                                unfold nb088_alpha_dummy_052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb088_support_mem_0051 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb088_alpha_dummy_041 A B C R) ≠
                                  (nb088_alpha_dummy_044 A B C R) from (by
                                  unfold nb088_alpha_dummy_044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb088_support_mem_0044 A B C R)
                                          1)))) (show (nb088_alpha_dummy_042 u A B R) ≠
                                  (nb088_alpha_dummy_046 u A B R) from (by
                                  unfold nb088_alpha_dummy_046;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb088_support_mem_0046 u A B R)
                                          1)))) (TAlphaVar.there (show
                                  (nb088_alpha_dummy_041 A B C R) ≠
                                    (nb088_alpha_dummy_043 A B C R) from (by
                                    unfold nb088_alpha_dummy_043;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0044 A B C R) 0)))) (show
                                  (nb088_alpha_dummy_042 u A B R) ≠
                                    (nb088_alpha_dummy_045 u A B R) from (by
                                    unfold nb088_alpha_dummy_045;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0046 u A B R) 0))))
                                (TAlphaVar.there (show (nb088_alpha_dummy_041 A B C R) ≠
                                      (nb088_alpha_dummy_049 A B C R) from (by
                                      unfold nb088_alpha_dummy_049;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0048 A B C R) 0)))) (show
                                    (nb088_alpha_dummy_042 u A B R) ≠
                                      (nb088_alpha_dummy_050 u A B R) from (by
                                      unfold nb088_alpha_dummy_050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0049 u A B R) 0))))
                                  (TAlphaVar.there (show (nb088_alpha_dummy_041 A B C R) ≠
                                        (nb088_alpha_dummy_047 A B C R) from (by
                                        unfold nb088_alpha_dummy_047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0045 A B C R) 0)))) (show
                                      (nb088_alpha_dummy_042 u A B R) ≠
                                        (nb088_alpha_dummy_048 u A B R) from (by
                                        unfold nb088_alpha_dummy_048;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0047 u A B R) 0))))
                                    (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪
                            ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) (by decide))
                        (freshVar_injective
                          (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪
                            ((Class.cv u)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb088_alpha_dummy_044 A B C R) ≠
                                    (nb088_alpha_dummy_053 A B C R) from (by
                                    unfold nb088_alpha_dummy_053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0052 A B C R) 0)))) (show
                                  (nb088_alpha_dummy_046 u A B R) ≠
                                    (nb088_alpha_dummy_055 u A B R) from (by
                                    unfold nb088_alpha_dummy_055;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0053 u A B R) 0))))
                                (TAlphaVar.there (show (nb088_alpha_dummy_044 A B C R) ≠
                                      (nb088_alpha_dummy_054 A B C R) from (by
                                      unfold nb088_alpha_dummy_054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0052 A B C R) 1)))) (show
                                    (nb088_alpha_dummy_046 u A B R) ≠
                                      (nb088_alpha_dummy_056 u A B R) from (by
                                      unfold nb088_alpha_dummy_056;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0053 u A B R) 1))))
                                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb088_alpha_dummy_044 A B C R))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb088_alpha_dummy_046 u A B R))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_060 A B C R) from (by
          unfold nb088_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056 A B
                    C R)
                  1)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_063 u A B R)
        from (by
          unfold nb088_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057 u A
                    B R)
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_059 A B C R) from (by
          unfold nb088_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_062 u A B R)
        from (by
          unfold nb088_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057 u
                    A B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_053 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053 A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_071 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_071 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_073 A B C R) from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_073 A B C R) from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                        [((nb088_alpha_dummy_057 A B C R),
        (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R),
        (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R),
        (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R),
        (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R),
        (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R),
        (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R),
        (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R),
        (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R),
        (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R) 0)))) (show (nb088_alpha_dummy_055 u A B R) ≠
        (nb088_alpha_dummy_058 u A B R) from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R) 0)))) (TAlphaVar.here _ _ _))))
                                  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                        [((nb088_alpha_dummy_057 A B C R),
        (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R),
        (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R),
        (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R),
        (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R),
        (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R),
        (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R),
        (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R),
        (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R),
        (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                          (TAlphaVar.there (show (nb088_alpha_dummy_041 A B C R) ≠
                                (nb088_alpha_dummy_051 A B C R) from (by
                                unfold nb088_alpha_dummy_051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb088_support_mem_0050 A B C R)
                                        0)))) (show (nb088_alpha_dummy_042 u A B R) ≠
                                (nb088_alpha_dummy_052 u A B R) from (by
                                unfold nb088_alpha_dummy_052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb088_support_mem_0051 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb088_alpha_dummy_041 A B C R) ≠
                                  (nb088_alpha_dummy_044 A B C R) from (by
                                  unfold nb088_alpha_dummy_044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb088_support_mem_0044 A B C R)
                                          1)))) (show (nb088_alpha_dummy_042 u A B R) ≠
                                  (nb088_alpha_dummy_046 u A B R) from (by
                                  unfold nb088_alpha_dummy_046;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb088_support_mem_0046 u A B R)
                                          1)))) (TAlphaVar.there (show
                                  (nb088_alpha_dummy_041 A B C R) ≠
                                    (nb088_alpha_dummy_043 A B C R) from (by
                                    unfold nb088_alpha_dummy_043;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0044 A B C R) 0)))) (show
                                  (nb088_alpha_dummy_042 u A B R) ≠
                                    (nb088_alpha_dummy_045 u A B R) from (by
                                    unfold nb088_alpha_dummy_045;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0046 u A B R) 0))))
                                (TAlphaVar.there (show (nb088_alpha_dummy_041 A B C R) ≠
                                      (nb088_alpha_dummy_049 A B C R) from (by
                                      unfold nb088_alpha_dummy_049;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0048 A B C R) 0)))) (show
                                    (nb088_alpha_dummy_042 u A B R) ≠
                                      (nb088_alpha_dummy_050 u A B R) from (by
                                      unfold nb088_alpha_dummy_050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0049 u A B R) 0))))
                                  (TAlphaVar.there (show (nb088_alpha_dummy_041 A B C R) ≠
                                        (nb088_alpha_dummy_047 A B C R) from (by
                                        unfold nb088_alpha_dummy_047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0045 A B C R) 0)))) (show
                                      (nb088_alpha_dummy_042 u A B R) ≠
                                        (nb088_alpha_dummy_048 u A B R) from (by
                                        unfold nb088_alpha_dummy_048;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0047 u A B R) 0))))
                                    (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪
                            ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) (by decide))
                        (freshVar_injective
                          (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪
                            ((Class.cv u)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb088_alpha_dummy_044 A B C R) ≠
                                    (nb088_alpha_dummy_053 A B C R) from (by
                                    unfold nb088_alpha_dummy_053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0052 A B C R) 0)))) (show
                                  (nb088_alpha_dummy_046 u A B R) ≠
                                    (nb088_alpha_dummy_055 u A B R) from (by
                                    unfold nb088_alpha_dummy_055;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0053 u A B R) 0))))
                                (TAlphaVar.there (show (nb088_alpha_dummy_044 A B C R) ≠
                                      (nb088_alpha_dummy_054 A B C R) from (by
                                      unfold nb088_alpha_dummy_054;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0052 A B C R) 1)))) (show
                                    (nb088_alpha_dummy_046 u A B R) ≠
                                      (nb088_alpha_dummy_056 u A B R) from (by
                                      unfold nb088_alpha_dummy_056;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0053 u A B R) 1))))
                                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb088_alpha_dummy_044 A B C R))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb088_alpha_dummy_046 u A B R))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_060 A B C R) from (by
          unfold nb088_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056 A B
                    C R)
                  1)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_063 u A B R)
        from (by
          unfold nb088_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057 u A
                    B R)
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_059 A B C R) from (by
          unfold nb088_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_062 u A B R)
        from (by
          unfold nb088_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057 u
                    A B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_049 A B C R), (nb088_alpha_dummy_050 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_053 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053 A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_071 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_071 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_073 A B C R) from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_073 A B C R) from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u A
                    B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                        [((nb088_alpha_dummy_057 A B C R),
        (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R),
        (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R),
        (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R),
        (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R),
        (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R),
        (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R),
        (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R),
        (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R),
        (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R) 0)))) (show (nb088_alpha_dummy_055 u A B R) ≠
        (nb088_alpha_dummy_058 u A B R) from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R) 0)))) (TAlphaVar.here _ _ _))))
                                  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                        [((nb088_alpha_dummy_057 A B C R),
        (nb088_alpha_dummy_058 u A B R)), ((nb088_alpha_dummy_053 A B C R),
        (nb088_alpha_dummy_055 u A B R)), ((nb088_alpha_dummy_054 A B C R),
        (nb088_alpha_dummy_056 u A B R)), ((nb088_alpha_dummy_044 A B C R),
        (nb088_alpha_dummy_046 u A B R)), ((nb088_alpha_dummy_043 A B C R),
        (nb088_alpha_dummy_045 u A B R)), ((nb088_alpha_dummy_049 A B C R),
        (nb088_alpha_dummy_050 u A B R)), ((nb088_alpha_dummy_047 A B C R),
        (nb088_alpha_dummy_048 u A B R)), ((nb088_alpha_dummy_041 A B C R),
        (nb088_alpha_dummy_042 u A B R)), ((nb088_alpha_dummy_001 A B C R),
        (nb088_alpha_dummy_002 u A B C R)), ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR5H088P001Part007`. -/


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
noncomputable def nb088_split_alpha_0004 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) :
    TAlphaWff
      [((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      (Wff.imp (Wff.classMem (Class.cv (nb088_alpha_dummy_044 A B C R))
          (Class.cv (nb088_alpha_dummy_000 A B C R))) (Wff.neg
          (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R))
            (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))
              (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb088_alpha_dummy_046 u A B R)) (Class.cv u)) (Wff.neg
          (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R))
            (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_044 A B C R) from (by
              unfold nb088_alpha_dummy_044;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 1))))
          (show u ≠ (nb088_alpha_dummy_046 u A B R) from (by
              unfold nb088_alpha_dummy_046;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 1))))
          (TAlphaVar.there
            (show (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_043 A B C R) from (by
                unfold nb088_alpha_dummy_043;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 0))))
            (show u ≠ (nb088_alpha_dummy_045 u A B R) from (by
                unfold nb088_alpha_dummy_045;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 0))))
            (TAlphaVar.there
              (show (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_075 A B C R) from (by
                  unfold nb088_alpha_dummy_075;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb088_support_mem_0080 A B C R) 0))))
              (show u ≠ (nb088_alpha_dummy_076 u A B R) from (by
                  unfold nb088_alpha_dummy_076;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb088_support_mem_0081 u A B R) 0)))) (TAlphaVar.there
                (show (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_047 A B C R) from (by
                    unfold nb088_alpha_dummy_047;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb088_support_mem_0077 A B C R) 0))))
                (show u ≠ (nb088_alpha_dummy_048 u A B R) from (by
                    unfold nb088_alpha_dummy_048;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb088_support_mem_0079 u A B R) 0))))
                (TAlphaVar.there
                  (show (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_041 A B C R) from
                    (by
                      unfold nb088_alpha_dummy_041;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0074 A B C R) 0))))
                  (show u ≠ (nb088_alpha_dummy_042 u A B R) from (by
                      unfold nb088_alpha_dummy_042;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0075 u A B R) 0))))
                  (TAlphaVar.there (show
                      (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_001 A B C R) from (by
                        unfold nb088_alpha_dummy_001;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0004 A B C R) 0))))
                    (show u ≠ (nb088_alpha_dummy_002 u A B C R) from (by
                        unfold nb088_alpha_dummy_002;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0005 u A B C R) 0))))
                    (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪
                ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) (by decide))
            (freshVar_injective (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪
                ((Class.cv u)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb088_alpha_dummy_044 A B C R) ≠
                                        (nb088_alpha_dummy_053 A B C R) from (by
                                        unfold nb088_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0052 A B C R) 0)))) (show
                                      (nb088_alpha_dummy_046 u A B R) ≠
                                        (nb088_alpha_dummy_055 u A B R) from (by
                                        unfold nb088_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0053 u A B R) 0))))
                                    (TAlphaVar.there (show (nb088_alpha_dummy_044 A B C R) ≠
        (nb088_alpha_dummy_054 A B C R) from (by
                                          unfold nb088_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0052 A B C R) 1)))) (show
                                        (nb088_alpha_dummy_046 u A B R) ≠
        (nb088_alpha_dummy_056 u A B R) from (by
                                          unfold nb088_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0053 u A B R) 1))))
                                      (TAlphaVar.there (show (nb088_alpha_dummy_044 A B C R) ≠
        (nb088_alpha_dummy_079 A B C R) from (by
          unfold nb088_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0084 A B C R) 0)))) (show (nb088_alpha_dummy_046 u A B R) ≠
        (nb088_alpha_dummy_080 u A B R) from (by
          unfold nb088_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0085 u A B R) 0)))) (TAlphaVar.there (show
        (nb088_alpha_dummy_044 A B C R) ≠ (nb088_alpha_dummy_077 A B C R) from (by
          unfold nb088_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0082 A B C R)
                  0)))) (show (nb088_alpha_dummy_046 u A B R) ≠ (nb088_alpha_dummy_078 u A B R)
        from (by
          unfold nb088_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0083 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb088_alpha_dummy_044 A B C R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb088_alpha_dummy_046 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_060 A B C R)
        from (by
          unfold nb088_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056
                    A B C R)
                  1)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_063 u A B R)
        from (by
          unfold nb088_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_059 A B C R) from (by
          unfold nb088_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_062 u A B R)
        from (by
          unfold nb088_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold
            nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_053 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053 A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_071 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_060
        A B C R) ≠ (nb088_alpha_dummy_071 A B C R) from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠ (nb088_alpha_dummy_073 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_073 A B C R) from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_057 A B C R)
        from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb088_alpha_dummy_044 A B C R) ≠
                                        (nb088_alpha_dummy_053 A B C R) from (by
                                        unfold nb088_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0052 A B C R) 0)))) (show
                                      (nb088_alpha_dummy_046 u A B R) ≠
                                        (nb088_alpha_dummy_055 u A B R) from (by
                                        unfold nb088_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0053 u A B R) 0))))
                                    (TAlphaVar.there (show (nb088_alpha_dummy_044 A B C R) ≠
        (nb088_alpha_dummy_054 A B C R) from (by
                                          unfold nb088_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0052 A B C R) 1)))) (show
                                        (nb088_alpha_dummy_046 u A B R) ≠
        (nb088_alpha_dummy_056 u A B R) from (by
                                          unfold nb088_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0053 u A B R) 1))))
                                      (TAlphaVar.there (show (nb088_alpha_dummy_044 A B C R) ≠
        (nb088_alpha_dummy_079 A B C R) from (by
          unfold nb088_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0084 A B C R) 0)))) (show (nb088_alpha_dummy_046 u A B R) ≠
        (nb088_alpha_dummy_080 u A B R) from (by
          unfold nb088_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0085 u A B R) 0)))) (TAlphaVar.there (show
        (nb088_alpha_dummy_044 A B C R) ≠ (nb088_alpha_dummy_077 A B C R) from (by
          unfold nb088_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0082 A B C R)
                  0)))) (show (nb088_alpha_dummy_046 u A B R) ≠ (nb088_alpha_dummy_078 u A B R)
        from (by
          unfold nb088_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0083 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb088_alpha_dummy_044 A B C R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb088_alpha_dummy_046 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_060 A B C R)
        from (by
          unfold nb088_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056
                    A B C R)
                  1)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_063 u A B R)
        from (by
          unfold nb088_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_059 A B C R) from (by
          unfold nb088_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0056
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_062 u A B R)
        from (by
          unfold nb088_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0057
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold
            nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_067 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0060
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0058
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_067 A B C R) from (by
          unfold
            nb088_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0064
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_065 A B C R) from (by
          unfold
            nb088_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0062
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_066 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_061 A B C R), (nb088_alpha_dummy_064 u A B R)),
        ((nb088_alpha_dummy_060 A B C R), (nb088_alpha_dummy_063 u A B R)),
        ((nb088_alpha_dummy_059 A B C R), (nb088_alpha_dummy_062 u A B R)),
        ((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_053 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053 A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠ (nb088_alpha_dummy_071 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_060
        A B C R) ≠ (nb088_alpha_dummy_071 A B C R) from (by
          unfold
            nb088_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0068
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_060 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0066
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_063 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_053
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠ (nb088_alpha_dummy_073 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_061
        A B C R) ≠ (nb088_alpha_dummy_073 A B C R) from (by
          unfold
            nb088_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0072
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_061 A B C R) ≠
        (nb088_alpha_dummy_069 A B C R) from (by
          unfold
            nb088_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0070
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_064 u A B R) ≠ (nb088_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb088_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠ (nb088_alpha_dummy_057 A B C R)
        from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_053 A B C R) ≠
        (nb088_alpha_dummy_057 A B C R) from (by
          unfold nb088_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0054 A B C R)
                  0)))) (show (nb088_alpha_dummy_055 u A B R) ≠ (nb088_alpha_dummy_058 u A B R)
        from (by
          unfold nb088_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_057 A B C R), (nb088_alpha_dummy_058 u A B R)),
        ((nb088_alpha_dummy_053 A B C R), (nb088_alpha_dummy_055 u A B R)),
        ((nb088_alpha_dummy_054 A B C R), (nb088_alpha_dummy_056 u A B R)),
        ((nb088_alpha_dummy_079 A B C R), (nb088_alpha_dummy_080 u A B R)),
        ((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
        ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
        ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
        ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
        ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
        ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb088_alpha_dummy_077 A B C R), (nb088_alpha_dummy_078 u A B R)),
                    ((nb088_alpha_dummy_044 A B C R), (nb088_alpha_dummy_046 u A B R)),
                    ((nb088_alpha_dummy_043 A B C R), (nb088_alpha_dummy_045 u A B R)),
                    ((nb088_alpha_dummy_075 A B C R), (nb088_alpha_dummy_076 u A B R)),
                    ((nb088_alpha_dummy_047 A B C R), (nb088_alpha_dummy_048 u A B R)),
                    ((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
                    ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
                    ((nb088_alpha_dummy_000 A B C R), u),
                    ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb088_focused_notmem_0005 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_041 A B C R) ∉ A.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb088_focused_notmem_0006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_041 A B C R) ∉ B.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb088_focused_notmem_0007 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_041 A B C R) ∉ R.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb088_wpp_notmem_0202 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_041 A B C R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb088_alpha_dummy_041, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb088_focused_notmem_0005 A B C R) (nb088_focused_notmem_0006 A B C R))
      (nb088_focused_notmem_0007 A B C R))

theorem nb088_focused_notmem_0008 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088_alpha_dummy_042 u A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb088_focused_notmem_0009 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088_alpha_dummy_042 u A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb088_focused_notmem_0010 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088_alpha_dummy_042 u A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb088_wpp_notmem_0203 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb088_alpha_dummy_042 u A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb088_alpha_dummy_042, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb088_focused_notmem_0008 u A B R) (nb088_focused_notmem_0009 u A B R))
      (nb088_focused_notmem_0010 u A B R))

theorem nb088_focused_notmem_0011 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_001 A B C R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb088_focused_notmem_0012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_001 A B C R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_focused_notmem_0013 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_001 A B C R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_wpp_notmem_0204 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_001 A B C R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb088_alpha_dummy_001, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb088_focused_notmem_0011 A B C R) (nb088_focused_notmem_0012 A B C R))
      (nb088_focused_notmem_0013 A B C R))

theorem nb088_focused_notmem_0014 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb088_focused_notmem_0015 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∉ B.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_focused_notmem_0016 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∉ R.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_wpp_notmem_0205 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_002 u A B C R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb088_alpha_dummy_002, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb088_focused_notmem_0014 u A B C R)
        (nb088_focused_notmem_0015 u A B C R)) (nb088_focused_notmem_0016 u A B C R))

theorem nb088_focused_notmem_0017 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_000 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb088_focused_notmem_0018 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_000 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb088_focused_notmem_0019 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_000 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb088_wpp_notmem_0206 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_000 A B C R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb088_alpha_dummy_000, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb088_focused_notmem_0017 A B C R) (nb088_focused_notmem_0018 A B C R))
      (nb088_focused_notmem_0019 A B C R))

theorem nb088_wpp_notmem_0207 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    u ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_u dv_B_u) dv_R_u)

theorem nb088_focused_notmem_0020 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_003 A B C R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪
            ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
                (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
        (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
      (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb088_focused_notmem_0021 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_003 A B C R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪
            ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
                (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
        (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
      (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_focused_notmem_0022 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_003 A B C R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪
            ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
                (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
        (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
      (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_wpp_notmem_0208 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_003 A B C R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb088_alpha_dummy_003, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb088_focused_notmem_0020 A B C R) (nb088_focused_notmem_0021 A B C R))
      (nb088_focused_notmem_0022 A B C R))

theorem nb088_focused_notmem_0023 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_004 u A B C R) ∉ A.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
                (syn_cfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
        (syn_cfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
      (syn_cfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb088_focused_notmem_0024 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_004 u A B C R) ∉ B.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
                (syn_cfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
        (syn_cfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
      (syn_cfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_focused_notmem_0025 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_004 u A B C R) ∉ R.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
                (syn_cfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
        (syn_cfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
      (syn_cfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb088_wpp_notmem_0209 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_004 u A B C R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb088_alpha_dummy_004, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb088_focused_notmem_0023 u A B C R)
        (nb088_focused_notmem_0024 u A B C R)) (nb088_focused_notmem_0025 u A B C R))

theorem nb088_compact_envfresh_0015 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    TEnvFresh
      [((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      ((syn_cfdrowrel R A B)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb088_alpha_dummy_041 A B C R) (nb088_alpha_dummy_042 u A B R)
      (nb088_wpp_notmem_0202 A B C R) (nb088_wpp_notmem_0203 u A B R)
      (TEnvFresh.consFresh (nb088_alpha_dummy_001 A B C R)
        (nb088_alpha_dummy_002 u A B C R) (nb088_wpp_notmem_0204 A B C R)
        (nb088_wpp_notmem_0205 u A B C R) (TEnvFresh.consFresh (nb088_alpha_dummy_000 A B C R) u
          (nb088_wpp_notmem_0206 A B C R) (nb088_wpp_notmem_0207 u A B R dv_A_u dv_B_u dv_R_u)
          (TEnvFresh.consFresh (nb088_alpha_dummy_003 A B C R)
            (nb088_alpha_dummy_004 u A B C R) (nb088_wpp_notmem_0208 A B C R)
            (nb088_wpp_notmem_0209 u A B C R) (TEnvFresh.nil ((syn_cfdrowrel R A B)).fv)))))

@[expose]
noncomputable def nb088_wpp_refl_0015 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    TReflOn
      [((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      ((syn_cfdrowrel R A B)).fv :=
  TEnvFresh.reflOn (nb088_compact_envfresh_0015 u A B C R dv_A_u dv_B_u dv_R_u)

@[expose]
noncomputable def nominal_df_fdcodemap2 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_C : Disjoint A.fv C.fv)
    (__dv_A_R : Disjoint A.fv R.fv) (dv_A_u : u ∉ A.fv) (__dv_B_C : Disjoint B.fv C.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_u : u ∉ B.fv) (__dv_C_R : Disjoint C.fv R.fv)
    (dv_C_u : u ∉ C.fv) (dv_R_u : u ∉ R.fv) :
    Nominal.NPrf
      (.classEq (syn_cfdcodemap2 R A B C)
        (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb088_split_alpha_0002 u A B C R) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                        (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_001 A B C R) from
                        (by
                          unfold nb088_alpha_dummy_001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0004 A B C R) 0))))
                      (show u ≠ (nb088_alpha_dummy_002 u A B C R) from (by
                          unfold nb088_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0005 u A B C R) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn
                    [((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
                      ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
                        (nb088_alpha_dummy_004 u A B C R))]
                    (syn_cpw1 (syn_cpw1 C)) (nb088_wpp_refl_0007 u A B C R dv_C_u)))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj (nb088_split_alpha_0003 u A B C R)
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb088_split_alpha_0004 u A B C R))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.neg
        (nb088_split_alpha_0004 u A B C R)))))))))))) (TAlphaClass.refl_of_reflOn
                        [((nb088_alpha_dummy_041 A B C R), (nb088_alpha_dummy_042 u A B R)),
                          ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
                          ((nb088_alpha_dummy_000 A B C R), u),
                          ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
                        (syn_cfdrowrel R A B)
                        (nb088_wpp_refl_0015 u A B C R dv_A_u dv_B_u dv_R_u))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
