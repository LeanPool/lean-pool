/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C089C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C089C001Part006`. -/


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
noncomputable def nb089_split_alpha_0002 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_051 A B R))
          (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089_alpha_dummy_051 A B R))
            (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_052 u A B R))
          (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb089_alpha_dummy_052 u A B R))
            (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_053 A B R) from
                        (by
                          unfold nb089_alpha_dummy_053;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb089_support_mem_0050 A B R) 0)))) (show
                        (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_054 u A B R) from
                        (by
                          unfold nb089_alpha_dummy_054;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb089_support_mem_0051 u A B R) 0))))
                      (TAlphaVar.there (show
                          (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_046 A B R) from (by
                            unfold nb089_alpha_dummy_046;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1)))) (show
                          (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_048 u A B R) from
                          (by
                            unfold nb089_alpha_dummy_048;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))))
                        (TAlphaVar.there (show
                            (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_045 A B R) from
                            (by
                              unfold nb089_alpha_dummy_045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0)))) (show
                            (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_047 u A B R)
                            from (by
                              unfold nb089_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0046 u A B R)
                                      0)))) (TAlphaVar.there (show
                              (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_051 A B R) from
                              (by
                                unfold nb089_alpha_dummy_051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0048 A B R)
                                        0)))) (show (nb089_alpha_dummy_044 u A B R) ≠
                                (nb089_alpha_dummy_052 u A B R) from (by
                                unfold nb089_alpha_dummy_052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0049 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_049 A B R)
                                from (by
                                  unfold nb089_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0045 A B R)
                                          0)))) (show (nb089_alpha_dummy_044 u A B R) ≠
                                  (nb089_alpha_dummy_050 u A B R) from (by
                                  unfold nb089_alpha_dummy_050;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0047 u A B R)
                                          0)))) (TAlphaVar.here _ _ _))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
                      ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) (by decide))
                  (freshVar_injective
                    (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪
                      ((Class.cv u)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show
                            (nb089_alpha_dummy_046 A B R) ≠ (nb089_alpha_dummy_055 A B R) from
                            (by
                              unfold nb089_alpha_dummy_055;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0052 A B R) 0)))) (show
                            (nb089_alpha_dummy_048 u A B R) ≠ (nb089_alpha_dummy_057 u A B R)
                            from (by
                              unfold nb089_alpha_dummy_057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                      0)))) (TAlphaVar.there (show
                              (nb089_alpha_dummy_046 A B R) ≠ (nb089_alpha_dummy_056 A B R) from
                              (by
                                unfold nb089_alpha_dummy_056;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0052 A B R)
                                        1)))) (show (nb089_alpha_dummy_048 u A B R) ≠
                                (nb089_alpha_dummy_058 u A B R) from (by
                                unfold nb089_alpha_dummy_058;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_062 A B R)
        from (by
          unfold nb089_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  1)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_065 u A B R)
        from (by
          unfold nb089_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_061 A B R) from (by
          unfold nb089_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_064 u A B R)
        from (by
          unfold nb089_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062
        A B R) ≠ (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062
        A B R) ≠ (nb089_alpha_dummy_073 A B R) from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_073 A B R)
        from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_075 A B R) from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_075 A B R) from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089_alpha_dummy_055 A B R) ≠
                                        (nb089_alpha_dummy_059 A B R) from (by
                                        unfold nb089_alpha_dummy_059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0054 A B R) 0)))) (show
                                      (nb089_alpha_dummy_057 u A B R) ≠
                                        (nb089_alpha_dummy_060 u A B R) from (by
                                        unfold nb089_alpha_dummy_060;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0055 u A B R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb089_alpha_dummy_059 A B R),
                                      (nb089_alpha_dummy_060 u A B R)),
                                    ((nb089_alpha_dummy_055 A B R),
                                      (nb089_alpha_dummy_057 u A B R)),
                                    ((nb089_alpha_dummy_056 A B R),
                                      (nb089_alpha_dummy_058 u A B R)),
                                    ((nb089_alpha_dummy_046 A B R),
                                      (nb089_alpha_dummy_048 u A B R)),
                                    ((nb089_alpha_dummy_045 A B R),
                                      (nb089_alpha_dummy_047 u A B R)),
                                    ((nb089_alpha_dummy_051 A B R),
                                      (nb089_alpha_dummy_052 u A B R)),
                                    ((nb089_alpha_dummy_049 A B R),
                                      (nb089_alpha_dummy_050 u A B R)),
                                    ((nb089_alpha_dummy_043 A B R),
                                      (nb089_alpha_dummy_044 u A B R)),
                                    ((nb089_alpha_dummy_003 A B R),
                                      (nb089_alpha_dummy_004 u A B R)),
                                    ((nb089_alpha_dummy_000 A B R), u),
                                    ((nb089_alpha_dummy_005 A B R),
                                      (nb089_alpha_dummy_006 u A B R)),
                                    ((nb089_alpha_dummy_001 A B R),
                                      (nb089_alpha_dummy_002 u A B R))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb089_alpha_dummy_055 A B R) ≠
                                      (nb089_alpha_dummy_059 A B R) from (by
                                      unfold nb089_alpha_dummy_059;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0054 A B R) 0)))) (show
                                    (nb089_alpha_dummy_057 u A B R) ≠
                                      (nb089_alpha_dummy_060 u A B R) from (by
                                      unfold nb089_alpha_dummy_060;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0055 u A B R) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089_alpha_dummy_055 A B R) ≠
                                        (nb089_alpha_dummy_059 A B R) from (by
                                        unfold nb089_alpha_dummy_059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0054 A B R) 0)))) (show
                                      (nb089_alpha_dummy_057 u A B R) ≠
                                        (nb089_alpha_dummy_060 u A B R) from (by
                                        unfold nb089_alpha_dummy_060;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0055 u A B R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb089_alpha_dummy_059 A B R),
                                      (nb089_alpha_dummy_060 u A B R)),
                                    ((nb089_alpha_dummy_055 A B R),
                                      (nb089_alpha_dummy_057 u A B R)),
                                    ((nb089_alpha_dummy_056 A B R),
                                      (nb089_alpha_dummy_058 u A B R)),
                                    ((nb089_alpha_dummy_046 A B R),
                                      (nb089_alpha_dummy_048 u A B R)),
                                    ((nb089_alpha_dummy_045 A B R),
                                      (nb089_alpha_dummy_047 u A B R)),
                                    ((nb089_alpha_dummy_051 A B R),
                                      (nb089_alpha_dummy_052 u A B R)),
                                    ((nb089_alpha_dummy_049 A B R),
                                      (nb089_alpha_dummy_050 u A B R)),
                                    ((nb089_alpha_dummy_043 A B R),
                                      (nb089_alpha_dummy_044 u A B R)),
                                    ((nb089_alpha_dummy_003 A B R),
                                      (nb089_alpha_dummy_004 u A B R)),
                                    ((nb089_alpha_dummy_000 A B R), u),
                                    ((nb089_alpha_dummy_005 A B R),
                                      (nb089_alpha_dummy_006 u A B R)),
                                    ((nb089_alpha_dummy_001 A B R),
                                      (nb089_alpha_dummy_002 u A B R))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show
                          (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_053 A B R) from (by
                            unfold nb089_alpha_dummy_053;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0050 A B R) 0)))) (show
                          (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_054 u A B R) from
                          (by
                            unfold nb089_alpha_dummy_054;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb089_support_mem_0051 u A B R) 0))))
                        (TAlphaVar.there (show
                            (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_046 A B R) from
                            (by
                              unfold nb089_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1)))) (show
                            (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_048 u A B R)
                            from (by
                              unfold nb089_alpha_dummy_048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb089_support_mem_0046 u A B R)
                                      1)))) (TAlphaVar.there (show
                              (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_045 A B R) from
                              (by
                                unfold nb089_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0044 A B R)
                                        0)))) (show (nb089_alpha_dummy_044 u A B R) ≠
                                (nb089_alpha_dummy_047 u A B R) from (by
                                unfold nb089_alpha_dummy_047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0046 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_051 A B R)
                                from (by
                                  unfold nb089_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0048 A B R)
                                          0)))) (show (nb089_alpha_dummy_044 u A B R) ≠
                                  (nb089_alpha_dummy_052 u A B R) from (by
                                  unfold nb089_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0049 u A B R)
                                          0)))) (TAlphaVar.there (show
                                  (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_049 A B R)
                                  from (by
                                    unfold nb089_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb089_support_mem_0045 A B R)
                                            0)))) (show (nb089_alpha_dummy_044 u A B R) ≠
                                    (nb089_alpha_dummy_050 u A B R) from (by
                                    unfold nb089_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb089_support_mem_0047 u A B R) 0))))
                                (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
                        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) (by decide))
                    (freshVar_injective
                      (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪
                        ((Class.cv u)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_046 A B R) ≠
                                (nb089_alpha_dummy_055 A B R) from (by
                                unfold nb089_alpha_dummy_055;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0052 A B R)
                                        0)))) (show (nb089_alpha_dummy_048 u A B R) ≠
                                (nb089_alpha_dummy_057 u A B R) from (by
                                unfold nb089_alpha_dummy_057;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                        0)))) (TAlphaVar.there (show
                                (nb089_alpha_dummy_046 A B R) ≠ (nb089_alpha_dummy_056 A B R)
                                from (by
                                  unfold nb089_alpha_dummy_056;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0052 A B R)
                                          1)))) (show (nb089_alpha_dummy_048 u A B R) ≠
                                  (nb089_alpha_dummy_058 u A B R) from (by
                                  unfold nb089_alpha_dummy_058;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb089_support_mem_0053 u A B R)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_062 A B R) from (by
          unfold nb089_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  1)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_065 u A B R)
        from (by
          unfold nb089_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_061 A B R) from (by
          unfold nb089_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_064 u A B R)
        from (by
          unfold nb089_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057 u A B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B
                    R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A
                    B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062
        A B R) ≠ (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_051 A B R), (nb089_alpha_dummy_052 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062
        A B R) ≠ (nb089_alpha_dummy_073 A B R) from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_073 A B R)
        from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A B R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u A B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_075 A B R) from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_075 A B R) from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A B R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u A B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
                                          unfold nb089_alpha_dummy_059;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0054 A B R) 0)))) (show
                                        (nb089_alpha_dummy_057 u A B R) ≠
        (nb089_alpha_dummy_060 u A B R) from (by
                                          unfold nb089_alpha_dummy_060;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0055 u A B R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb089_alpha_dummy_059 A B R),
                                        (nb089_alpha_dummy_060 u A B R)),
                                      ((nb089_alpha_dummy_055 A B R),
                                        (nb089_alpha_dummy_057 u A B R)),
                                      ((nb089_alpha_dummy_056 A B R),
                                        (nb089_alpha_dummy_058 u A B R)),
                                      ((nb089_alpha_dummy_046 A B R),
                                        (nb089_alpha_dummy_048 u A B R)),
                                      ((nb089_alpha_dummy_045 A B R),
                                        (nb089_alpha_dummy_047 u A B R)),
                                      ((nb089_alpha_dummy_051 A B R),
                                        (nb089_alpha_dummy_052 u A B R)),
                                      ((nb089_alpha_dummy_049 A B R),
                                        (nb089_alpha_dummy_050 u A B R)),
                                      ((nb089_alpha_dummy_043 A B R),
                                        (nb089_alpha_dummy_044 u A B R)),
                                      ((nb089_alpha_dummy_003 A B R),
                                        (nb089_alpha_dummy_004 u A B R)),
                                      ((nb089_alpha_dummy_000 A B R), u),
                                      ((nb089_alpha_dummy_005 A B R),
                                        (nb089_alpha_dummy_006 u A B R)),
                                      ((nb089_alpha_dummy_001 A B R),
                                        (nb089_alpha_dummy_002 u A B R))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089_alpha_dummy_055 A B R) ≠
                                        (nb089_alpha_dummy_059 A B R) from (by
                                        unfold nb089_alpha_dummy_059;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0054 A B R) 0)))) (show
                                      (nb089_alpha_dummy_057 u A B R) ≠
                                        (nb089_alpha_dummy_060 u A B R) from (by
                                        unfold nb089_alpha_dummy_060;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0055 u A B R) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
                                          unfold nb089_alpha_dummy_059;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0054 A B R) 0)))) (show
                                        (nb089_alpha_dummy_057 u A B R) ≠
        (nb089_alpha_dummy_060 u A B R) from (by
                                          unfold nb089_alpha_dummy_060;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0055 u A B R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb089_alpha_dummy_059 A B R),
                                        (nb089_alpha_dummy_060 u A B R)),
                                      ((nb089_alpha_dummy_055 A B R),
                                        (nb089_alpha_dummy_057 u A B R)),
                                      ((nb089_alpha_dummy_056 A B R),
                                        (nb089_alpha_dummy_058 u A B R)),
                                      ((nb089_alpha_dummy_046 A B R),
                                        (nb089_alpha_dummy_048 u A B R)),
                                      ((nb089_alpha_dummy_045 A B R),
                                        (nb089_alpha_dummy_047 u A B R)),
                                      ((nb089_alpha_dummy_051 A B R),
                                        (nb089_alpha_dummy_052 u A B R)),
                                      ((nb089_alpha_dummy_049 A B R),
                                        (nb089_alpha_dummy_050 u A B R)),
                                      ((nb089_alpha_dummy_043 A B R),
                                        (nb089_alpha_dummy_044 u A B R)),
                                      ((nb089_alpha_dummy_003 A B R),
                                        (nb089_alpha_dummy_004 u A B R)),
                                      ((nb089_alpha_dummy_000 A B R), u),
                                      ((nb089_alpha_dummy_005 A B R),
                                        (nb089_alpha_dummy_006 u A B R)),
                                      ((nb089_alpha_dummy_001 A B R),
                                        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part007`. -/


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
noncomputable def nb089_split_alpha_0003 (u : Var) (A : Class) (B : Class) (R : Class) :
    TAlphaWff
      [((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_046 A B R))
          (Class.cv (nb089_alpha_dummy_000 A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
            (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb089_alpha_dummy_048 u A B R)) (Class.cv u)) (Wff.neg
          (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
            (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_046 A B R) from (by
              unfold nb089_alpha_dummy_046;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))))
          (show u ≠ (nb089_alpha_dummy_048 u A B R) from (by
              unfold nb089_alpha_dummy_048;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))))
          (TAlphaVar.there
            (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_045 A B R) from (by
                unfold nb089_alpha_dummy_045;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))))
            (show u ≠ (nb089_alpha_dummy_047 u A B R) from (by
                unfold nb089_alpha_dummy_047;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))))
            (TAlphaVar.there
              (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_077 A B R) from (by
                  unfold nb089_alpha_dummy_077;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0080 A B R) 0))))
              (show u ≠ (nb089_alpha_dummy_078 u A B R) from (by
                  unfold nb089_alpha_dummy_078;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb089_support_mem_0081 u A B R) 0)))) (TAlphaVar.there
                (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_049 A B R) from (by
                    unfold nb089_alpha_dummy_049;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0077 A B R) 0))))
                (show u ≠ (nb089_alpha_dummy_050 u A B R) from (by
                    unfold nb089_alpha_dummy_050;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb089_support_mem_0079 u A B R) 0))))
                (TAlphaVar.there
                  (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_043 A B R) from (by
                      unfold nb089_alpha_dummy_043;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb089_support_mem_0074 A B R) 0))))
                  (show u ≠ (nb089_alpha_dummy_044 u A B R) from (by
                      unfold nb089_alpha_dummy_044;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb089_support_mem_0075 u A B R) 0))))
                  (TAlphaVar.there
                    (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_003 A B R) from (by
                        unfold nb089_alpha_dummy_003;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb089_support_mem_0004 A B R) 0))))
                    (show u ≠ (nb089_alpha_dummy_004 u A B R) from (by
                        unfold nb089_alpha_dummy_004;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb089_support_mem_0005 u A B R) 0))))
                    (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
                ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) (by decide)) (freshVar_injective
              (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv)
              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089_alpha_dummy_046 A B R) ≠
                                        (nb089_alpha_dummy_055 A B R) from (by
                                        unfold nb089_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0052 A B R) 0)))) (show
                                      (nb089_alpha_dummy_048 u A B R) ≠
                                        (nb089_alpha_dummy_057 u A B R) from (by
                                        unfold nb089_alpha_dummy_057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0053 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089_alpha_dummy_046 A B R) ≠
        (nb089_alpha_dummy_056 A B R) from (by
                                          unfold nb089_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0052 A B R) 1)))) (show
                                        (nb089_alpha_dummy_048 u A B R) ≠
        (nb089_alpha_dummy_058 u A B R) from (by
                                          unfold nb089_alpha_dummy_058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0053 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089_alpha_dummy_046 A B R) ≠
        (nb089_alpha_dummy_081 A B R) from (by
          unfold nb089_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0084 A B R) 0)))) (show (nb089_alpha_dummy_048 u A B R) ≠
        (nb089_alpha_dummy_082 u A B R) from (by
          unfold nb089_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0085 u A B R) 0)))) (TAlphaVar.there (show
        (nb089_alpha_dummy_046 A B R) ≠ (nb089_alpha_dummy_079 A B R) from (by
          unfold nb089_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0082 A B R) 0)))) (show (nb089_alpha_dummy_048 u A B R) ≠
        (nb089_alpha_dummy_080 u A B R) from (by
          unfold nb089_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0083 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_046 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_062 A B R)
        from (by
          unfold nb089_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  1)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_065 u A B R)
        from (by
          unfold nb089_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_061 A B R) from (by
          unfold nb089_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_064 u A B R)
        from (by
          unfold nb089_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold
            nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054
                    A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_073 A B R)
        from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062
        A B R) ≠ (nb089_alpha_dummy_073 A B R) from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠ (nb089_alpha_dummy_075 A B R)
        from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_075 A B R) from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_059 A B R)
        from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb089_alpha_dummy_046 A B R) ≠
                                        (nb089_alpha_dummy_055 A B R) from (by
                                        unfold nb089_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0052 A B R) 0)))) (show
                                      (nb089_alpha_dummy_048 u A B R) ≠
                                        (nb089_alpha_dummy_057 u A B R) from (by
                                        unfold nb089_alpha_dummy_057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0053 u A B R) 0))))
                                    (TAlphaVar.there (show (nb089_alpha_dummy_046 A B R) ≠
        (nb089_alpha_dummy_056 A B R) from (by
                                          unfold nb089_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0052 A B R) 1)))) (show
                                        (nb089_alpha_dummy_048 u A B R) ≠
        (nb089_alpha_dummy_058 u A B R) from (by
                                          unfold nb089_alpha_dummy_058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb089_support_mem_0053 u A B R) 1))))
                                      (TAlphaVar.there (show (nb089_alpha_dummy_046 A B R) ≠
        (nb089_alpha_dummy_081 A B R) from (by
          unfold nb089_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0084 A B R) 0)))) (show (nb089_alpha_dummy_048 u A B R) ≠
        (nb089_alpha_dummy_082 u A B R) from (by
          unfold nb089_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0085 u A B R) 0)))) (TAlphaVar.there (show
        (nb089_alpha_dummy_046 A B R) ≠ (nb089_alpha_dummy_079 A B R) from (by
          unfold nb089_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0082 A B R) 0)))) (show (nb089_alpha_dummy_048 u A B R) ≠
        (nb089_alpha_dummy_080 u A B R) from (by
          unfold nb089_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0083 u A B R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_046 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_062 A B R)
        from (by
          unfold nb089_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  1)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_065 u A B R)
        from (by
          unfold nb089_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  1)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_061 A B R) from (by
          unfold nb089_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0056
                    A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_064 u A B R)
        from (by
          unfold nb089_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0057
                    u A B R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold
            nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054
                    A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055
                    u A B R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_069 A B R)
        from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0060
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0061
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0058
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0059
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_069 A B R) from (by
          unfold
            nb089_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0064
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_070 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0065
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_067 A B R) from (by
          unfold
            nb089_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0062
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_068 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0063
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_063 A B R), (nb089_alpha_dummy_066 u A B R)),
        ((nb089_alpha_dummy_062 A B R), (nb089_alpha_dummy_065 u A B R)),
        ((nb089_alpha_dummy_061 A B R), (nb089_alpha_dummy_064 u A B R)),
        ((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057
        u A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_073 A B R)
        from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_062
        A B R) ≠ (nb089_alpha_dummy_073 A B R) from (by
          unfold
            nb089_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0068
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_074 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0069
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_062 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0066
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0067
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb089_alpha_dummy_055
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠ (nb089_alpha_dummy_075 A B R)
        from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_063
        A B R) ≠ (nb089_alpha_dummy_075 A B R) from (by
          unfold
            nb089_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0072
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_076 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0073
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.there (show (nb089_alpha_dummy_063 A B R) ≠
        (nb089_alpha_dummy_071 A B R) from (by
          unfold
            nb089_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0070
                    A
                    B
                    R)
                  0)))) (show (nb089_alpha_dummy_066 u A B R) ≠ (nb089_alpha_dummy_072 u A B R)
        from (by
          unfold
            nb089_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0071
                    u
                    A
                    B
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_059 A B R)
        from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb089_alpha_dummy_055 A B R) ≠
        (nb089_alpha_dummy_059 A B R) from (by
          unfold nb089_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0054 A B R)
                  0)))) (show (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_060 u A B R)
        from (by
          unfold nb089_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb089_support_mem_0055 u A B R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb089_alpha_dummy_059 A B R), (nb089_alpha_dummy_060 u A B R)),
        ((nb089_alpha_dummy_055 A B R), (nb089_alpha_dummy_057 u A B R)),
        ((nb089_alpha_dummy_056 A B R), (nb089_alpha_dummy_058 u A B R)),
        ((nb089_alpha_dummy_081 A B R), (nb089_alpha_dummy_082 u A B R)),
        ((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
        ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
        ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
        ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
        ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
        ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u), ((nb089_alpha_dummy_005 A B R),
        (nb089_alpha_dummy_006 u A B R)), ((nb089_alpha_dummy_001 A B R),
        (nb089_alpha_dummy_002 u A B R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb089_alpha_dummy_079 A B R), (nb089_alpha_dummy_080 u A B R)),
                    ((nb089_alpha_dummy_046 A B R), (nb089_alpha_dummy_048 u A B R)),
                    ((nb089_alpha_dummy_045 A B R), (nb089_alpha_dummy_047 u A B R)),
                    ((nb089_alpha_dummy_077 A B R), (nb089_alpha_dummy_078 u A B R)),
                    ((nb089_alpha_dummy_049 A B R), (nb089_alpha_dummy_050 u A B R)),
                    ((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
                    ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
                    ((nb089_alpha_dummy_000 A B R), u),
                    ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
                    ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb089_focused_notmem_0007 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∉ A.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb089_focused_notmem_0008 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∉ B.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb089_focused_notmem_0009 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∉ R.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb089_wpp_notmem_0212 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_043, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0007 A B R) (nb089_focused_notmem_0008 A B R))
      (nb089_focused_notmem_0009 A B R))

theorem nb089_focused_notmem_0010 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb089_focused_notmem_0011 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb089_focused_notmem_0012 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb089_wpp_notmem_0213 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_044, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb089_focused_notmem_0010 u A B R) (nb089_focused_notmem_0011 u A B R))
      (nb089_focused_notmem_0012 u A B R))

theorem nb089_focused_notmem_0013 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
            ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_focused_notmem_0014 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
            ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0214 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_003, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0000 A B R) (nb089_focused_notmem_0013 A B R))
      (nb089_focused_notmem_0014 A B R))

theorem nb089_focused_notmem_0015 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
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

theorem nb089_focused_notmem_0016 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
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

theorem nb089_wpp_notmem_0215 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_004, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb089_focused_notmem_0001 u A B R) (nb089_focused_notmem_0015 u A B R))
      (nb089_focused_notmem_0016 u A B R))

theorem nb089_focused_notmem_0017 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb089_focused_notmem_0018 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb089_wpp_notmem_0216 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_000, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0002 A B R) (nb089_focused_notmem_0017 A B R))
      (nb089_focused_notmem_0018 A B R))

theorem nb089_wpp_notmem_0217 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    u ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_u dv_B_u) dv_R_u)

theorem nb089_focused_notmem_0019 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_005 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
            ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
                (syn_cpw1 (syn_cpw1 (syn_cuni A))))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
                (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
        (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089_alpha_dummy_003 A B R))
      (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_focused_notmem_0020 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_005 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
            ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
                (syn_cpw1 (syn_cpw1 (syn_cuni A))))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
                (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
        (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089_alpha_dummy_003 A B R))
      (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0218 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_005 A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_005, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0003 A B R) (nb089_focused_notmem_0019 A B R))
      (nb089_focused_notmem_0020 A B R))

theorem nb089_focused_notmem_0021 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_006 u A B R) ∉ B.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
                (syn_cfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
        (syn_cfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
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

theorem nb089_focused_notmem_0022 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_006 u A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
                (syn_cfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
        (syn_cfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
      (syn_cfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdrowfib R A B (Class.cv u)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb089_wpp_notmem_0219 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_006 u A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_006, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb089_focused_notmem_0004 u A B R) (nb089_focused_notmem_0021 u A B R))
      (nb089_focused_notmem_0022 u A B R))

theorem nb089_focused_notmem_0023 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_wbr R (syn_cwe) A)).fv ∪
            ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
                (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪
          ((syn_c0)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
      (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb089_focused_notmem_0017 A B R)) (h_eq ▸ hu)
  · rw [fv_syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    right
    exact hu

theorem nb089_focused_notmem_0024 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_wbr R (syn_cwe) A)).fv ∪
            ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
                (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪
          ((syn_c0)).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [fv_syn_wbr R (syn_cwe) A]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb089_wpp_notmem_0220 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb089_alpha_dummy_001, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0005 A B R) (nb089_focused_notmem_0023 A B R))
      (nb089_focused_notmem_0024 A B R))

theorem nb089_focused_notmem_0025 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_B_u : u ∉ B.fv) : (nb089_alpha_dummy_002 u A B R) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A)))
                (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv u))]
  rw [Finset.mem_union]
  right
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => (dv_B_u) (h_eq ▸ hu)
  · rw [fv_syn_cfdrowfib R A B (Class.cv u)]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    left
    rw [Finset.mem_union]
    right
    exact hu

theorem nb089_focused_notmem_0026 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_002 u A B R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A)))
                (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [fv_syn_wbr R (syn_cwe) A]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb089_wpp_notmem_0221 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_B_u : u ∉ B.fv) : (nb089_alpha_dummy_002 u A B R) ∉ ((syn_cfdrowrel R A B)).fv :=
  by
  simpa only [nb089_alpha_dummy_002, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro (nb089_focused_notmem_0006 u A B R)
        (nb089_focused_notmem_0025 u A B R dv_B_u)) (nb089_focused_notmem_0026 u A B R))

theorem nb089_compact_envfresh_0015 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    TEnvFresh
      [((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((syn_cfdrowrel R A B)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089_alpha_dummy_043 A B R) (nb089_alpha_dummy_044 u A B R)
      (nb089_wpp_notmem_0212 A B R) (nb089_wpp_notmem_0213 u A B R)
      (TEnvFresh.consFresh (nb089_alpha_dummy_003 A B R) (nb089_alpha_dummy_004 u A B R)
        (nb089_wpp_notmem_0214 A B R) (nb089_wpp_notmem_0215 u A B R)
        (TEnvFresh.consFresh (nb089_alpha_dummy_000 A B R) u (nb089_wpp_notmem_0216 A B R)
          (nb089_wpp_notmem_0217 u A B R dv_A_u dv_B_u dv_R_u)
          (TEnvFresh.consFresh (nb089_alpha_dummy_005 A B R)
            (nb089_alpha_dummy_006 u A B R) (nb089_wpp_notmem_0218 A B R)
            (nb089_wpp_notmem_0219 u A B R) (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R)
              (nb089_alpha_dummy_002 u A B R) (nb089_wpp_notmem_0220 A B R)
              (nb089_wpp_notmem_0221 u A B R dv_B_u)
              (TEnvFresh.nil ((syn_cfdrowrel R A B)).fv))))))

@[expose]
noncomputable def nb089_wpp_refl_0015 (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_u : u ∉ A.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    TReflOn
      [((nb089_alpha_dummy_043 A B R), (nb089_alpha_dummy_044 u A B R)),
        ((nb089_alpha_dummy_003 A B R), (nb089_alpha_dummy_004 u A B R)),
        ((nb089_alpha_dummy_000 A B R), u),
        ((nb089_alpha_dummy_005 A B R), (nb089_alpha_dummy_006 u A B R)),
        ((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((syn_cfdrowrel R A B)).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0015 u A B R dv_A_u dv_B_u dv_R_u)

theorem nb089_wpp_notmem_0222 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ ((Wff.neg (syn_wbr R (syn_cwe) A))).fv := by
  simpa only [nb089_alpha_dummy_001, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro (And.intro (nb089_focused_notmem_0024 A B R) (nb089_focused_notmem_0005 A B R))
      (nb089_compact_fv_empty_0026 A B R))

theorem nb089_wpp_notmem_0223 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_002 u A B R) ∉ ((Wff.neg (syn_wbr R (syn_cwe) A))).fv := by
  simpa only [nb089_alpha_dummy_002, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro
      (And.intro (nb089_focused_notmem_0026 u A B R) (nb089_focused_notmem_0006 u A B R))
      (nb089_compact_fv_empty_0027 u A B R))

theorem nb089_compact_envfresh_0016 (u : Var) (A : Class) (B : Class) (R : Class) :
    TEnvFresh [((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((Wff.neg (syn_wbr R (syn_cwe) A))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R)
      (nb089_wpp_notmem_0222 A B R) (nb089_wpp_notmem_0223 u A B R)
      (TEnvFresh.nil ((Wff.neg (syn_wbr R (syn_cwe) A))).fv))

@[expose]
noncomputable def nb089_wpp_refl_0016 (u : Var) (A : Class) (B : Class) (R : Class) :
    TReflOn [((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((Wff.neg (syn_wbr R (syn_cwe) A))).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0016 u A B R)

theorem nb089_wpp_notmem_0224 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ ((Wff.neg (Wff.neg (syn_wbr R (syn_cwe) A)))).fv := by
  simpa only [nb089_alpha_dummy_001, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro (And.intro (nb089_focused_notmem_0024 A B R) (nb089_focused_notmem_0005 A B R))
      (nb089_compact_fv_empty_0026 A B R))

theorem nb089_wpp_notmem_0225 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_002 u A B R) ∉ ((Wff.neg (Wff.neg (syn_wbr R (syn_cwe) A)))).fv :=
  by
  simpa only [nb089_alpha_dummy_002, fv_wff_neg, fv_syn_wbr, Finset.mem_union, not_or,
    fv_syn_cwe] using
    (And.intro
      (And.intro (nb089_focused_notmem_0026 u A B R) (nb089_focused_notmem_0006 u A B R))
      (nb089_compact_fv_empty_0027 u A B R))

theorem nb089_compact_envfresh_0018 (u : Var) (A : Class) (B : Class) (R : Class) :
    TEnvFresh [((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((Wff.neg (Wff.neg (syn_wbr R (syn_cwe) A)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb089_alpha_dummy_001 A B R) (nb089_alpha_dummy_002 u A B R)
      (nb089_wpp_notmem_0224 A B R) (nb089_wpp_notmem_0225 u A B R)
      (TEnvFresh.nil ((Wff.neg (Wff.neg (syn_wbr R (syn_cwe) A)))).fv))

@[expose]
noncomputable def nb089_wpp_refl_0018 (u : Var) (A : Class) (B : Class) (R : Class) :
    TReflOn [((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
      ((Wff.neg (Wff.neg (syn_wbr R (syn_cwe) A)))).fv :=
  TEnvFresh.reflOn (nb089_compact_envfresh_0018 u A B R)

@[expose]
noncomputable def nominal_df_fdglobalrowmap (u : Var) (A : Class) (B : Class) (R : Class)
    (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_R : Disjoint A.fv R.fv) (dv_A_u : u ∉ A.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    Nominal.NPrf
      (.classEq (syn_cfdglobalrowmap R A B) (syn_cif (syn_wbr R (syn_cwe) A)
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
          (syn_c0))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                    (nb089_alpha_dummy_003 A B R) ≠
                                      (nb089_alpha_dummy_005 A B R) from (by
                                      unfold nb089_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0002 A B R) 0))))) (Ne.symm
                                  (show (nb089_alpha_dummy_004 u A B R) ≠
                                      (nb089_alpha_dummy_006 u A B R) from (by
                                      unfold nb089_alpha_dummy_006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0003 u A B R) 0)))))
                                (TAlphaVar.there (Ne.symm (show (nb089_alpha_dummy_000 A B R) ≠
                                        (nb089_alpha_dummy_005 A B R) from (by
                                        unfold nb089_alpha_dummy_005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0000 A B R) 0))))) (Ne.symm
                                    (show u ≠ (nb089_alpha_dummy_006 u A B R) from (by
                                        unfold nb089_alpha_dummy_006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb089_support_mem_0001 u A B R) 0)))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb089_split_alpha_0001 u A B R)))))
                          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb089_alpha_dummy_000 A B R) ≠
                                      (nb089_alpha_dummy_003 A B R) from (by
                                      unfold nb089_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0004 A B R) 0))))
                                  (show u ≠ (nb089_alpha_dummy_004 u A B R) from (by
                                      unfold nb089_alpha_dummy_004;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb089_support_mem_0005 u A B R) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn
                                [((nb089_alpha_dummy_003 A B R),
                                    (nb089_alpha_dummy_004 u A B R)),
                                  ((nb089_alpha_dummy_000 A B R), u),
                                  ((nb089_alpha_dummy_005 A B R),
                                    (nb089_alpha_dummy_006 u A B R)),
                                  ((nb089_alpha_dummy_001 A B R),
                                    (nb089_alpha_dummy_002 u A B R))]
                                (syn_cpw1 (syn_cpw1 (syn_cuni A)))
                                (nb089_wpp_refl_0007 u A B R dv_A_u)))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb089_split_alpha_0002 u A B R))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb089_split_alpha_0003 u A B R))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb089_split_alpha_0003 u A B R)))))))))))) (TAlphaClass.refl_of_reflOn
                                    [((nb089_alpha_dummy_043 A B R),
                                        (nb089_alpha_dummy_044 u A B R)),
                                      ((nb089_alpha_dummy_003 A B R),
                                        (nb089_alpha_dummy_004 u A B R)),
                                      ((nb089_alpha_dummy_000 A B R), u),
                                      ((nb089_alpha_dummy_005 A B R),
                                        (nb089_alpha_dummy_006 u A B R)),
                                      ((nb089_alpha_dummy_001 A B R),
                                        (nb089_alpha_dummy_002 u A B R))] (syn_cfdrowrel R A B)
                                    (nb089_wpp_refl_0015 u A B R dv_A_u dv_B_u dv_R_u)))))))))))
                (TAlphaWff.refl_of_reflOn
                  [((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
                  (Wff.neg (syn_wbr R (syn_cwe) A)) (nb089_wpp_refl_0016 u A B R)))))
          (TAlphaWff.neg (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
                  (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.refl_of_reflOn
                [((nb089_alpha_dummy_001 A B R), (nb089_alpha_dummy_002 u A B R))]
                (Wff.neg (Wff.neg (syn_wbr R (syn_cwe) A))) (nb089_wpp_refl_0018 u A B R))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
