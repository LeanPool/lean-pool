/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C087C001Part003

/-! NF weak partition development: NAR4C087C001Part004. -/


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
noncomputable def nominal_df_fdrowfib (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_C : Disjoint A.fv C.fv)
    (__dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (__dv_B_C : Disjoint B.fv C.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (__dv_C_R : Disjoint C.fv R.fv)
    (dv_C_d : d ∉ C.fv) (dv_R_d : d ∉ R.fv) :
    Nominal.NPrf
      (.classEq (syn_cfdrowfib R A B C)
        (.cab d (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_000 A B C R) ≠ (nb087_alpha_dummy_009 A B C R) from (by
          unfold nb087_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0006 A B C R)
                  0)))) (show d ≠ (nb087_alpha_dummy_010 d) from (by
          unfold nb087_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0007 d) 0)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_000 A B C R) ≠ (nb087_alpha_dummy_002 A B C R) from (by
          unfold nb087_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  1)))) (show d ≠ (nb087_alpha_dummy_004 C d) from (by
          unfold nb087_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d) 1)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_000 A B C R) ≠ (nb087_alpha_dummy_001 A B C R) from (by
          unfold nb087_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  0)))) (show d ≠ (nb087_alpha_dummy_003 C d) from (by
          unfold nb087_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_000 A B C R) ≠
        (nb087_alpha_dummy_007 A B C R) from (by
          unfold nb087_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0004 A B C
                    R)
                  0)))) (show d ≠ (nb087_alpha_dummy_008 C d) from (by
          unfold nb087_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0005 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_000 A B C R) ≠
        (nb087_alpha_dummy_005 A B C R) from (by
          unfold nb087_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0001 A B
                    C R)
                  0)))) (show d ≠ (nb087_alpha_dummy_006 C d) from (by
          unfold nb087_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0003 C d)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                    (TAlphaVar.there (freshVar_injective (((syn_csn (Class.cv
        (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) (by decide)) (freshVar_injective
                                        (((syn_csn (Class.cv d))).fv ∪ (C).fv) (by decide))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_011 A B C R) from (by
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
                  (nb087_support_mem_0009 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_012 A B C R) from (by
          unfold nb087_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C
                    R)
                  1)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_014 C d) from (by
          unfold nb087_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A
        B C R) ≠ (nb087_alpha_dummy_018 A B C R) from (by
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
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002
        A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R),
        (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008
        C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_c1c) (by
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
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002
        A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R),
        (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008
        C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_c0) (by
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
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)),
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
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_000 A B C R) ≠ (nb087_alpha_dummy_009 A B C R) from (by
          unfold nb087_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0006 A B C R)
                  0)))) (show d ≠ (nb087_alpha_dummy_010 d) from (by
          unfold nb087_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0007 d) 0)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_000 A B C R) ≠ (nb087_alpha_dummy_002 A B C R) from (by
          unfold nb087_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  1)))) (show d ≠ (nb087_alpha_dummy_004 C d) from (by
          unfold nb087_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d) 1)))) (TAlphaVar.there (show
        (nb087_alpha_dummy_000 A B C R) ≠ (nb087_alpha_dummy_001 A B C R) from (by
          unfold nb087_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0000 A B C R)
                  0)))) (show d ≠ (nb087_alpha_dummy_003 C d) from (by
          unfold nb087_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0002 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_000 A B C R) ≠
        (nb087_alpha_dummy_007 A B C R) from (by
          unfold nb087_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0004 A B C
                    R)
                  0)))) (show d ≠ (nb087_alpha_dummy_008 C d) from (by
          unfold nb087_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0005 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_000 A B C R) ≠
        (nb087_alpha_dummy_005 A B C R) from (by
          unfold nb087_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0001 A B
                    C R)
                  0)))) (show d ≠ (nb087_alpha_dummy_006 C d) from (by
          unfold nb087_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0003 C d)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                    (TAlphaVar.there (freshVar_injective (((syn_csn (Class.cv
        (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) (by decide)) (freshVar_injective
                                        (((syn_csn (Class.cv d))).fv ∪ (C).fv) (by decide))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb087_alpha_dummy_002 A B C R) ≠ (nb087_alpha_dummy_011 A B C R) from (by
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
                  (nb087_support_mem_0009 C d)
                  0)))) (TAlphaVar.there (show (nb087_alpha_dummy_002 A B C R) ≠
        (nb087_alpha_dummy_012 A B C R) from (by
          unfold nb087_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0008 A B C
                    R)
                  1)))) (show (nb087_alpha_dummy_004 C d) ≠ (nb087_alpha_dummy_014 C d) from (by
          unfold nb087_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb087_support_mem_0009 C d)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb087_alpha_dummy_004 C d))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb087_alpha_dummy_011 A
        B C R) ≠ (nb087_alpha_dummy_018 A B C R) from (by
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
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002
        A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R),
        (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008
        C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_c1c) (by
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
        ((nb087_alpha_dummy_012 A B C R), (nb087_alpha_dummy_014 C d)), ((nb087_alpha_dummy_002
        A B C R), (nb087_alpha_dummy_004 C d)), ((nb087_alpha_dummy_001 A B C R),
        (nb087_alpha_dummy_003 C d)), ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008
        C d)), ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_c0) (by
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
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)),
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
        ((nb087_alpha_dummy_002 A B C R), (nb087_alpha_dummy_004 C d)),
        ((nb087_alpha_dummy_001 A B C R), (nb087_alpha_dummy_003 C d)),
        ((nb087_alpha_dummy_007 A B C R), (nb087_alpha_dummy_008 C d)),
        ((nb087_alpha_dummy_005 A B C R), (nb087_alpha_dummy_006 C d)),
        ((nb087_alpha_dummy_000 A B C R), d)] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg
                      (TAlphaWff.neg (nb087_split_alpha_0000 A B C R d dv_C_d))))))))
          (TAlphaClass.refl_of_reflOn [((nb087_alpha_dummy_000 A B C R), d)]
            (syn_cfdrowrel R A B) (nb087_wpp_refl_0007 A B C R d dv_A_d dv_B_d dv_R_d))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
