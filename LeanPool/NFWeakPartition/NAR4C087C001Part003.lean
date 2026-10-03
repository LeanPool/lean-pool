/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C087C001Block001

/-! NF weak partition development: NAR4C087C001Part003. -/


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
noncomputable def nb087_split_alpha_0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) :
    TAlphaWff
      [((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)]
      (Wff.imp (Wff.classMem (Class.cv (nb087_alpha_dummy_033 A B C R))
          (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C
              (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb087_alpha_dummy_033 A B C R))
            (Class.cab (nb087_alpha_dummy_001 A B C R)
              (syn_wrex (nb087_alpha_dummy_002 A B C R) C
                (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb087_alpha_dummy_034 C d))
          (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C
              (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d))
                (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb087_alpha_dummy_034 C d))
            (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C
                (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d))
                  (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn
                [((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
                  ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
                  ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
                  ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
                  ((nb087_alpha_dummy_000 A B C R), d)]
                C (nb087_focused_refl_0000 A B C R d dv_C_d))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv)
                    (by decide))
                  (freshVar_injective (((syn_csn (Class.cv d))).fv ∪ (C).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_011 A B C R) from (by
          unfold nb087_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_013 C d) from (by
          unfold nb087_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_012 A B C R) from (by
          unfold nb087_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_014 C d) from (by
          unfold nb087_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 1)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_037 A B C R) from (by
          unfold nb087_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_038 C d) from (by
          unfold nb087_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_035 A B C R) from (by
          unfold nb087_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B C
                    R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_036 C d) from (by
          unfold nb087_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087_alpha_dummy_002 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087_alpha_dummy_004 C d))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_011 A B C R) ≠ (nb087_alpha_dummy_018 A B C R) from (by
          unfold
            nb087_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_021 C d) from (by
          unfold
            nb087_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_017 A B C R) from (by
          unfold
            nb087_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_020 C d) from (by
          unfold
            nb087_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold
            nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold
            nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)),
        ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)),
        ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)),
        ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018
        A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R),
        (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016
        C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037
        A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R),
        (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004
        C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005
        A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] (syn_c0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A
        B C R) ≠ (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠ (nb087_alpha_dummy_031 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_031 A B C R) from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A B
                    C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_011 A B C R) from (by
          unfold nb087_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_013 C d) from (by
          unfold nb087_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_012 A B C R) from (by
          unfold nb087_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_014 C d) from (by
          unfold nb087_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 1)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_037 A B C R) from (by
          unfold nb087_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_038 C d) from (by
          unfold nb087_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_035 A B C R) from (by
          unfold nb087_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B C
                    R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_036 C d) from (by
          unfold nb087_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087_alpha_dummy_002 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087_alpha_dummy_004 C d))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_011 A B C R) ≠ (nb087_alpha_dummy_018 A B C R) from (by
          unfold
            nb087_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_021 C d) from (by
          unfold
            nb087_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_017 A B C R) from (by
          unfold
            nb087_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_020 C d) from (by
          unfold
            nb087_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold
            nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold
            nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)),
        ((nb087_alpha_dummy_018 A B C R), (nb087_alpha_dummy_021 C d)),
        ((nb087_alpha_dummy_017 A B C R), (nb087_alpha_dummy_020 C d)),
        ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018
        A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R),
        (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016
        C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037
        A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R),
        (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004
        C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005
        A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] (syn_c0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A
        B C R) ≠ (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠ (nb087_alpha_dummy_031 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_031 A B C R) from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A B
                    C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
                          ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
                          ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
                          ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
                          ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
                          ((nb087_alpha_dummy_000 A B C R), d)] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_reflOn
                  [((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
                    ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
                    ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
                    ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
                    ((nb087_alpha_dummy_000 A B C R), d)]
                  C (nb087_focused_refl_0000 A B C R d dv_C_d))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv)
                      (by decide)) (freshVar_injective (((syn_csn (Class.cv d))).fv ∪ (C).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_011 A B C R)
        from (by
          unfold nb087_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_013 C d) from (by
          unfold nb087_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_012 A B C R) from (by
          unfold nb087_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_014 C d) from (by
          unfold nb087_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_037 A B C R) from (by
          unfold nb087_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C
                    R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_038 C d) from (by
          unfold nb087_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_035 A B C R) from (by
          unfold nb087_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B
                    C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_036 C d) from (by
          unfold nb087_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_011 A B C R) ≠ (nb087_alpha_dummy_018 A B C R) from (by
          unfold
            nb087_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_021 C d) from (by
          unfold
            nb087_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_017 A B C R) from (by
          unfold
            nb087_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_020 C d) from (by
          unfold
            nb087_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold
            nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold
            nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018
        A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R),
        (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016
        C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037
        A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R),
        (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004
        C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005
        A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] (syn_c1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018
        A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R),
        (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016
        C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037
        A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R),
        (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004
        C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005
        A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] (syn_c0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A
        B C R) ≠ (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠ (nb087_alpha_dummy_031 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_031 A B C R) from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_011 A B C R)
        from (by
          unfold nb087_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_013 C d) from (by
          unfold nb087_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d) 0)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_012 A B C R) from (by
          unfold nb087_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C R)
                  1)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_014 C d) from (by
          unfold nb087_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_037 A B C R) from (by
          unfold nb087_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0032 A B C
                    R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_038 C d) from (by
          unfold nb087_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0033 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_035 A B C R) from (by
          unfold nb087_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0030 A B
                    C R)
                  0)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_036 C d) from (by
          unfold nb087_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0031 C d)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_011 A B C R) ≠ (nb087_alpha_dummy_018 A B C R) from (by
          unfold
            nb087_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  1)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_021 C d) from (by
          unfold
            nb087_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  1)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_017 A B C R) from (by
          unfold
            nb087_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0012
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_020 C d) from (by
          unfold
            nb087_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0013
                    C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold
            nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold
            nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018
        A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R),
        (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016
        C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037
        A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R),
        (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004
        C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005
        A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] (syn_c1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_025 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0017
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0015
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_025 A B C R) from (by
          unfold
            nb087_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_026 C d) from (by
          unfold
            nb087_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0021
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_023 A B C R) from (by
          unfold
            nb087_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_024 C d) from (by
          unfold
            nb087_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0019
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_019 A B C R), (nb087_alpha_dummy_022 C d)), ((nb087_alpha_dummy_018
        A B C R), (nb087_alpha_dummy_021 C d)), ((nb087_alpha_dummy_017 A B C R),
        (nb087_alpha_dummy_020 C d)), ((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016
        C d)), ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_037
        A B C R), (nb087_alpha_dummy_038 C d)), ((nb087_alpha_dummy_035 A B C R),
        (nb087_alpha_dummy_036 C d)), ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004
        C d)), ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)), ((nb087_alpha_dummy_005
        A B C R), (nb087_alpha_dummy_006 C d)), ((nb087_alpha_dummy_000 A B C R), d)] (syn_c0)
        (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_018 A
        B C R) ≠ (nb087_alpha_dummy_029 A B C R) from (by
          unfold
            nb087_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_030 C d) from (by
          unfold
            nb087_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0025
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_018 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0023
                    C
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_011
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠ (nb087_alpha_dummy_031 A B C R)
        from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_019 A
        B C R) ≠ (nb087_alpha_dummy_031 A B C R) from (by
          unfold
            nb087_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0028
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_032 C d) from (by
          unfold
            nb087_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0029
                    C
                    d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_019 A B C R) ≠
        (nb087_alpha_dummy_027 A B C R) from (by
          unfold
            nb087_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb087_alpha_dummy_022 C d) ≠ (nb087_alpha_dummy_028 C d) from (by
          unfold
            nb087_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0027
                    C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010 A
                    B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011 C
                    d)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A B C R) ≠
        (nb087_alpha_dummy_015 A B C R) from (by
          unfold nb087_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0010
                    A B C R)
                  0)))) (show (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_016 C d) from (by
          unfold nb087_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0011
                    C d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb087_alpha_dummy_015 A B C R), (nb087_alpha_dummy_016 C d)),
        ((nb087_alpha_dummy_011 A B C R), (nb087_alpha_dummy_013 C d)),
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)),
        ((nb087_alpha_dummy_037 A B C R), (nb087_alpha_dummy_038 C d)),
        ((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb087_alpha_dummy_035 A B C R), (nb087_alpha_dummy_036 C d)),
                            ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
                            ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
                            ((nb087_alpha_dummy_033 A B C R), (nb087_alpha_dummy_034 C d)),
                            ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
                            ((nb087_alpha_dummy_000 A B C R), d)]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb087_focused_notmem_0009 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087_alpha_dummy_000 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb087_focused_notmem_0010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087_alpha_dummy_000 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb087_focused_notmem_0011 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087_alpha_dummy_000 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb087_wpp_notmem_0090 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb087_alpha_dummy_000 A B C R) ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [nb087_alpha_dummy_000, fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb087_focused_notmem_0009 A B C R) (nb087_focused_notmem_0010 A B C R))
      (nb087_focused_notmem_0011 A B C R))

theorem nb087_wpp_notmem_0091 (A : Class) (B : Class) (R : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    d ∉ ((syn_cfdrowrel R A B)).fv := by
  simpa only [fv_syn_cfdrowrel, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_d dv_B_d) dv_R_d)

theorem nb087_compact_envfresh_0008 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    TEnvFresh [((nb087_alpha_dummy_000 A B C R), d)] ((syn_cfdrowrel R A B)).fv := by
  exact
    (TEnvFresh.consFresh (nb087_alpha_dummy_000 A B C R) d (nb087_wpp_notmem_0090 A B C R)
      (nb087_wpp_notmem_0091 A B R d dv_A_d dv_B_d dv_R_d)
      (TEnvFresh.nil ((syn_cfdrowrel R A B)).fv))

@[expose]
noncomputable def nb087_wpp_refl_0007 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    TReflOn [((nb087_alpha_dummy_000 A B C R), d)] ((syn_cfdrowrel R A B)).fv :=
  TEnvFresh.reflOn (nb087_compact_envfresh_0008 A B C R d dv_A_d dv_B_d dv_R_d)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
