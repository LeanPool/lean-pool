/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR5H088P001Block001

/-! NF weak partition development: NAR5H088P001Part004. -/


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
noncomputable def nb088_split_alpha_0000 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) :
    TAlphaWff
      [((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      (Wff.neg (Wff.classMem (Class.cv (nb088_alpha_dummy_035 A B C R))
          (Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R)
              (Class.cv (nb088_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))
                  (syn_csn (syn_c0c))))))))
      (Wff.neg (Wff.classMem (Class.cv (nb088_alpha_dummy_036 u A B C R))
          (Class.cab (nb088_alpha_dummy_007 u A B C R)
            (syn_wrex (nb088_alpha_dummy_008 u A B C R)
              (Class.cv (nb088_alpha_dummy_002 u A B C R))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R))
                (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))
                  (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb088_alpha_dummy_001 A B C R) ≠ (nb088_alpha_dummy_006 A B C R) from
                    (by
                      unfold nb088_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1)))) (show
                    (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_008 u A B C R) from
                    (by
                      unfold nb088_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))))
                  (TAlphaVar.there (show
                      (nb088_alpha_dummy_001 A B C R) ≠ (nb088_alpha_dummy_005 A B C R) from (by
                        unfold nb088_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0)))) (show
                      (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_007 u A B C R) from
                      (by
                        unfold nb088_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))))
                    (TAlphaVar.there (show
                        (nb088_alpha_dummy_001 A B C R) ≠ (nb088_alpha_dummy_035 A B C R) from
                        (by
                          unfold nb088_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0038 A B C R) 0)))) (show
                        (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_036 u A B C R)
                        from (by
                          unfold nb088_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0039 u A B C R) 0))))
                      (TAlphaVar.there (show (nb088_alpha_dummy_001 A B C R) ≠
                            (nb088_alpha_dummy_009 A B C R) from (by
                            unfold nb088_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0035 A B C R) 0)))) (show
                          (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_010 u A B C R)
                          from (by
                            unfold nb088_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0037 u A B C R)
                                    0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪
                      ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv) (by decide))
                  (freshVar_injective (((Class.cv u)).fv ∪
                      ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_013 A B C R) from (by
          unfold nb088_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_015 u A B C R) from (by
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
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_039 A B C R) from (by
          unfold nb088_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_040 u A B C R) from (by
          unfold nb088_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_037 A B C R) from (by
          unfold nb088_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_038 u A B C R) from (by
          unfold nb088_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
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
                  1)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_023 u A
        B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_022 u
        A B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_018
        u A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A
        B C R) ≠ (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_033 A B C R) from (by
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
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_013 A B C R) from (by
          unfold nb088_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_015 u A B C R) from (by
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
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_039 A B C R) from (by
          unfold nb088_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_040 u A B C R) from (by
          unfold nb088_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_037 A B C R) from (by
          unfold nb088_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_038 u A B C R) from (by
          unfold nb088_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
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
                  1)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_023 u A
        B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_022 u
        A B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_018
        u A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A
        B C R) ≠ (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_033 A B C R) from (by
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
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed [((nb088_alpha_dummy_037 A B C R),
                            (nb088_alpha_dummy_038 u A B C R)),
                          ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
                          ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
                          ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
                          ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
                          ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
                          ((nb088_alpha_dummy_000 A B C R), u),
                          ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c]))))))))))))

@[expose]
noncomputable def nb088_split_alpha_0001 (u : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) :
    TAlphaWff
      [((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u),
        ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
      (Wff.imp (Wff.classMem (Class.cv (nb088_alpha_dummy_035 A B C R))
          (Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R)
              (Class.cv (nb088_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb088_alpha_dummy_035 A B C R))
            (Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R)
                (Class.cv (nb088_alpha_dummy_001 A B C R))
                (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb088_alpha_dummy_036 u A B C R))
          (Class.cab (nb088_alpha_dummy_007 u A B C R)
            (syn_wrex (nb088_alpha_dummy_008 u A B C R)
              (Class.cv (nb088_alpha_dummy_002 u A B C R))
              (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R))
                (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb088_alpha_dummy_036 u A B C R))
            (Class.cab (nb088_alpha_dummy_007 u A B C R)
              (syn_wrex (nb088_alpha_dummy_008 u A B C R)
                (Class.cv (nb088_alpha_dummy_002 u A B C R))
                (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb088_alpha_dummy_001 A B C R) ≠ (nb088_alpha_dummy_006 A B C R) from
                    (by
                      unfold nb088_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1)))) (show
                    (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_008 u A B C R) from
                    (by
                      unfold nb088_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))))
                  (TAlphaVar.there (show
                      (nb088_alpha_dummy_001 A B C R) ≠ (nb088_alpha_dummy_005 A B C R) from (by
                        unfold nb088_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0)))) (show
                      (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_007 u A B C R) from
                      (by
                        unfold nb088_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))))
                    (TAlphaVar.there (show
                        (nb088_alpha_dummy_001 A B C R) ≠ (nb088_alpha_dummy_035 A B C R) from
                        (by
                          unfold nb088_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0038 A B C R) 0)))) (show
                        (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_036 u A B C R)
                        from (by
                          unfold nb088_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb088_support_mem_0039 u A B C R) 0))))
                      (TAlphaVar.there (show (nb088_alpha_dummy_001 A B C R) ≠
                            (nb088_alpha_dummy_009 A B C R) from (by
                            unfold nb088_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0035 A B C R) 0)))) (show
                          (nb088_alpha_dummy_002 u A B C R) ≠ (nb088_alpha_dummy_010 u A B C R)
                          from (by
                            unfold nb088_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb088_support_mem_0037 u A B C R)
                                    0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪
                      ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv) (by decide))
                  (freshVar_injective (((Class.cv u)).fv ∪
                      ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_013 A B C R) from (by
          unfold nb088_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_015 u A B C R) from (by
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
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_039 A B C R) from (by
          unfold nb088_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_040 u A B C R) from (by
          unfold nb088_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_037 A B C R) from (by
          unfold nb088_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_038 u A B C R) from (by
          unfold nb088_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
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
                  1)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_023 u A
        B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_022 u
        A B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_018
        u A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A
        B C R) ≠ (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_033 A B C R) from (by
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
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_013 A B C R) from (by
          unfold nb088_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0012 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_015 u A B C R) from (by
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
                  1)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_039 A B C R) from (by
          unfold nb088_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0042 A B C R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_040 u A B C R) from (by
          unfold nb088_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0043 u A B C
                    R)
                  0)))) (TAlphaVar.there (show (nb088_alpha_dummy_006 A B C R) ≠
        (nb088_alpha_dummy_037 A B C R) from (by
          unfold nb088_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0040 A B C
                    R)
                  0)))) (show (nb088_alpha_dummy_008 u A B C R) ≠
        (nb088_alpha_dummy_038 u A B C R) from (by
          unfold nb088_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0041 u A B
                    C R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
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
                  1)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_023 u A
        B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_022 u
        A B C R) from (by
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
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠ (nb088_alpha_dummy_018
        u A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb088_alpha_dummy_020 A B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_027 A B C R) from (by
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
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A B C R) ≠
        (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_020 A
        B C R) ≠ (nb088_alpha_dummy_031 A B C R) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_021 A
        B C R) ≠ (nb088_alpha_dummy_033 A B C R) from (by
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
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb088_alpha_dummy_013 A B C R) ≠
        (nb088_alpha_dummy_017 A B C R) from (by
          unfold nb088_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0014 A
                    B C R)
                  0)))) (show (nb088_alpha_dummy_015 u A B C R) ≠
        (nb088_alpha_dummy_018 u A B C R) from (by
          unfold nb088_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb088_support_mem_0015 u
                    A B C R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb088_alpha_dummy_017 A B C R), (nb088_alpha_dummy_018 u A B C R)),
        ((nb088_alpha_dummy_013 A B C R), (nb088_alpha_dummy_015 u A B C R)),
        ((nb088_alpha_dummy_014 A B C R), (nb088_alpha_dummy_016 u A B C R)),
        ((nb088_alpha_dummy_039 A B C R), (nb088_alpha_dummy_040 u A B C R)),
        ((nb088_alpha_dummy_037 A B C R), (nb088_alpha_dummy_038 u A B C R)),
        ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
        ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
        ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
        ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
        ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
        ((nb088_alpha_dummy_000 A B C R), u), ((nb088_alpha_dummy_003 A B C R),
        (nb088_alpha_dummy_004 u A B C R))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed [((nb088_alpha_dummy_037 A B C R),
                            (nb088_alpha_dummy_038 u A B C R)),
                          ((nb088_alpha_dummy_006 A B C R), (nb088_alpha_dummy_008 u A B C R)),
                          ((nb088_alpha_dummy_005 A B C R), (nb088_alpha_dummy_007 u A B C R)),
                          ((nb088_alpha_dummy_035 A B C R), (nb088_alpha_dummy_036 u A B C R)),
                          ((nb088_alpha_dummy_009 A B C R), (nb088_alpha_dummy_010 u A B C R)),
                          ((nb088_alpha_dummy_001 A B C R), (nb088_alpha_dummy_002 u A B C R)),
                          ((nb088_alpha_dummy_000 A B C R), u),
                          ((nb088_alpha_dummy_003 A B C R), (nb088_alpha_dummy_004 u A B C R))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb088_split_alpha_0000 u A B C R))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
