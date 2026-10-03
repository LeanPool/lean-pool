/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR5H088P001Part004

/-! NF weak partition development: NAR5H088P001Part005. -/


public section


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
noncomputable def nb088_split_alpha_0002 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) :
    TAlphaWff
      [((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      (Wff.classEq (Class.cv (nb088_alpha_dummy_003 A B C R))
        (syn_cop (Class.cv (nb088_alpha_dummy_000 A B C R))
          (Class.cv (nb088_alpha_dummy_001 A B C R))))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_004 u A B C R))
        (syn_cop (Class.cv u) (Class.cv (nb088_alpha_dummy_002 u A B C R)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb088_alpha_dummy_001 A B C R) ≠ (nb088_alpha_dummy_003 A B C R) from (by
              unfold nb088_alpha_dummy_003;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0002 A B C R) 0)))))
        (Ne.symm
          (show (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_004 u A B C R) from (by
              unfold nb088_alpha_dummy_004;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0003 u A B C R) 0)))))
        (TAlphaVar.there (Ne.symm
            (show (nb088_alpha_dummy_000 A B C R) ≠ (nb088_alpha_dummy_003 A B C R) from (by
                unfold nb088_alpha_dummy_003;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0000 A B C R) 0)))))
          (Ne.symm (show u ≠ (nb088_alpha_dummy_004 u A B C R) from (by
                unfold nb088_alpha_dummy_004;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb088_support_mem_0001 u A B C R) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb088_alpha_dummy_000 A B C R) ≠
                                    (nb088_alpha_dummy_006 A B C R) from (by
                                    unfold nb088_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0006 A B C R) 1))))
                                (show u ≠ (nb088_alpha_dummy_008 u A B C R) from (by
                                    unfold nb088_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0008 u A B C R) 1))))
                                (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
                                      (nb088_alpha_dummy_005 A B C R) from (by
                                      unfold nb088_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0006 A B C R) 0))))
                                  (show u ≠ (nb088_alpha_dummy_007 u A B C R) from (by
                                      unfold nb088_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0008 u A B C R) 0))))
                                  (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
                                        (nb088_alpha_dummy_011 A B C R) from (by
                                        unfold nb088_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0010 A B C R) 0))))
                                    (show u ≠ (nb088_alpha_dummy_012 u A B C R) from (by
                                        unfold nb088_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0011 u A B C R) 0))))
                                    (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
        (nb088_alpha_dummy_009 A B C R) from (by
                                          unfold nb088_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0007 A B C R) 0))))
                                      (show u ≠ (nb088_alpha_dummy_010 u A B C R) from (by
                                          unfold nb088_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0009 u A B C R) 0))))
                                      (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
        (nb088_alpha_dummy_001 A B C R) from (by
          unfold nb088_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0004 A B C R) 0))))
                                        (show u ≠ (nb088_alpha_dummy_002 u A B C R) from (by
          unfold nb088_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0005 u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪
                                    ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv)
                                  (by decide)) (freshVar_injective (((Class.cv u)).fv ∪
                                    ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_013 A B C R) from (by
          unfold nb088_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R) 0)))) (show
        (nb088_alpha_dummy_008 u A B C R) ≠ (nb088_alpha_dummy_015 u A B C R) from (by
          unfold nb088_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_014 A B C R) from (by
          unfold nb088_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  1)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_016 u A B C R) from (by
          unfold nb088_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                                      (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_013 A B C R) ≠ (nb088_alpha_dummy_020 A B C R) from (by
          unfold
            nb088_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  1)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_023 u A B
        C R) from (by
          unfold
            nb088_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_019 A B C R) from (by
          unfold
            nb088_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_022 u A
        B C R) from (by
          unfold
            nb088_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold
            nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_018 u
        A B C R) from (by
          unfold
            nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015
                    u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)),
        ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)),
        ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)),
        ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_027 A B C R) from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021
        A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_027 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021
        A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)),
        ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)),
        ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)),
        ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015
        u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_031 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_032 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020
        A B C R) ≠ (nb088_alpha_dummy_031 A B C R) from (by
          unfold
            nb088_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_032 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠ (nb088_alpha_dummy_033 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_034 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021
        A B C R) ≠ (nb088_alpha_dummy_033 A B C R) from (by
          unfold
            nb088_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_034 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_013 A B C R) ≠ (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B C
                    R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb088_alpha_dummy_000 A B C R) ≠
                                    (nb088_alpha_dummy_006 A B C R) from (by
                                    unfold nb088_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0006 A B C R) 1))))
                                (show u ≠ (nb088_alpha_dummy_008 u A B C R) from (by
                                    unfold nb088_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb088_support_mem_0008 u A B C R) 1))))
                                (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
                                      (nb088_alpha_dummy_005 A B C R) from (by
                                      unfold nb088_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0006 A B C R) 0))))
                                  (show u ≠ (nb088_alpha_dummy_007 u A B C R) from (by
                                      unfold nb088_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb088_support_mem_0008 u A B C R) 0))))
                                  (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
                                        (nb088_alpha_dummy_011 A B C R) from (by
                                        unfold nb088_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0010 A B C R) 0))))
                                    (show u ≠ (nb088_alpha_dummy_012 u A B C R) from (by
                                        unfold nb088_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb088_support_mem_0011 u A B C R) 0))))
                                    (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
        (nb088_alpha_dummy_009 A B C R) from (by
                                          unfold nb088_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0007 A B C R) 0))))
                                      (show u ≠ (nb088_alpha_dummy_010 u A B C R) from (by
                                          unfold nb088_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb088_support_mem_0009 u A B C R) 0))))
                                      (TAlphaVar.there (show (nb088_alpha_dummy_000 A B C R) ≠
        (nb088_alpha_dummy_001 A B C R) from (by
          unfold nb088_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0004 A B C R) 0))))
                                        (show u ≠ (nb088_alpha_dummy_002 u A B C R) from (by
          unfold nb088_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0005 u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪
                                    ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv)
                                  (by decide)) (freshVar_injective (((Class.cv u)).fv ∪
                                    ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_013 A B C R) from (by
          unfold nb088_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R) 0)))) (show
        (nb088_alpha_dummy_008 u A B C R) ≠ (nb088_alpha_dummy_015 u A B C R) from (by
          unfold nb088_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_014 A B C R) from (by
          unfold nb088_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  1)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_016 u A B C R) from (by
          unfold nb088_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0013 u A B C R)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                                      (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_006 A B C R))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_008 u A B C R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_013 A B C R) ≠ (nb088_alpha_dummy_020 A B C R) from (by
          unfold
            nb088_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  1)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_023 u A B
        C R) from (by
          unfold
            nb088_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_019 A B C R) from (by
          unfold
            nb088_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0016
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_022 u A
        B C R) from (by
          unfold
            nb088_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0017
                    u A B C R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold
            nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014
                    A B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_018 u
        A B C R) from (by
          unfold
            nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015
                    u A B C R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)),
        ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)),
        ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)),
        ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_027 A B C R) from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021
        A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_027 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0021
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0019
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021
        A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
          unfold
            nb088_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_028 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0025
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_025 A B C R) from (by
          unfold
            nb088_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_026 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0023
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_021 A B C R), (nb088_alpha_dummy_024 u A B C R)),
        ((nb088_alpha_dummy_020 A B C R), (nb088_alpha_dummy_023 u A B C R)),
        ((nb088_alpha_dummy_019 A B C R), (nb088_alpha_dummy_022 u A B C R)),
        ((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015
        u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_031 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_032 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020
        A B C R) ≠ (nb088_alpha_dummy_031 A B C R) from (by
          unfold
            nb088_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_032 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0029
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_023 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0027
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb088_alpha_dummy_013
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠ (nb088_alpha_dummy_033 A B C R)
        from (by
          unfold
            nb088_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_034 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021
        A B C R) ≠ (nb088_alpha_dummy_033 A B C R) from (by
          unfold
            nb088_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0032
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_034 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0033
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_021 A B C R) ≠
        (nb088_alpha_dummy_029 A B C R) from (by
          unfold
            nb088_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0030
                    A
                    B
                    C
                    R)
                  0)))) (show (nb088_alpha_dummy_024 u A B C R) ≠ (nb088_alpha_dummy_030 u A B C
        R) from (by
          unfold
            nb088_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0031
                    u
                    A
                    B
                    C
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                        (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_013 A B C R) ≠ (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B C
                    R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A B
                    C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u A
                    B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_011 A B C R), (nb088_alpha_dummy_012 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb088_split_alpha_0001 u A B C R)))))))))

theorem nb088_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_001 A B C R) ∉ C.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 C)]
  rw [fv_syn_cpw1 C]
  exact hu

theorem nb088_wpp_notmem_0106 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_001 A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_001, fv_syn_cpw1] using
    (nb088_focused_notmem_0000 A B C R)

theorem nb088_focused_notmem_0001 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∉ C.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪
          ((syn_cfdrowfib R A B (Class.cv u))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 C)]
  rw [fv_syn_cpw1 C]
  exact hu

theorem nb088_wpp_notmem_0107 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_002 u A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_002, fv_syn_cpw1] using
    (nb088_focused_notmem_0001 u A B C R)

theorem nb088_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_000 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb088_wpp_notmem_0108 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_000 A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_000, fv_syn_cpw1] using
    (nb088_focused_notmem_0002 A B C R)

theorem nb088_wpp_notmem_0109 (u : Var) (C : Class) (dv_C_u : u ∉ C.fv) :
    u ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by simpa only [fv_syn_cpw1] using dv_C_u

theorem nb088_focused_notmem_0003 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_003 A B C R) ∉ C.fv :=
  by
  change
    freshVar
        (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪
            ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
                (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R))
        (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 C)]
  rw [fv_syn_cpw1 C]
  exact hu

theorem nb088_wpp_notmem_0110 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_003 A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_003, fv_syn_cpw1] using
    (nb088_focused_notmem_0003 A B C R)

theorem nb088_focused_notmem_0004 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) : (nb088_alpha_dummy_004 u A B C R) ∉ C.fv :=
  by
  change
    freshVar
        (({ u } : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
                (syn_cfdrowfib R A B (Class.cv u))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C)))
      (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R))
        (syn_cfdrowfib R A B (Class.cv u)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cpw1 (syn_cpw1 C)]
  rw [fv_syn_cpw1 C]
  exact hu

theorem nb088_wpp_notmem_0111 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb088_alpha_dummy_004 u A B C R) ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
  simpa only [nb088_alpha_dummy_004, fv_syn_cpw1] using
    (nb088_focused_notmem_0004 u A B C R)

theorem nb088_compact_envfresh_0007 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (dv_C_u : u ∉ C.fv) :
    TEnvFresh
      [((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      ((syn_cpw1 (syn_cpw1 C))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb088_alpha_dummy_001 A B C R) (nb088_alpha_dummy_002 u A B C R)
      (nb088_wpp_notmem_0106 A B C R) (nb088_wpp_notmem_0107 u A B C R)
      (TEnvFresh.consFresh (nb088_alpha_dummy_000 A B C R) u
        (nb088_wpp_notmem_0108 A B C R) (nb088_wpp_notmem_0109 u C dv_C_u)
        (TEnvFresh.consFresh (nb088_alpha_dummy_003 A B C R)
          (nb088_alpha_dummy_004 u A B C R) (nb088_wpp_notmem_0110 A B C R)
          (nb088_wpp_notmem_0111 u A B C R) (TEnvFresh.nil ((syn_cpw1 (syn_cpw1 C))).fv))))

@[expose]
noncomputable def nb088_wpp_refl_0007 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (dv_C_u : u ∉ C.fv) :
    TReflOn
      [((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      ((syn_cpw1 (syn_cpw1 C))).fv :=
  TEnvFresh.reflOn (nb088_compact_envfresh_0007 u A B C R dv_C_u)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
