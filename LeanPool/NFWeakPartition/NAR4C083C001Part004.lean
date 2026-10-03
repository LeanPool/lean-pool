/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C083C001Part003

/-! NF weak partition development: NAR4C083C001Part004. -/


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
noncomputable def nb083_split_alpha_0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) (dv_B_b : b ∉ B.fv)
    (dv_B_c : c ∉ B.fv) (dv_C_b : b ∉ C.fv) (dv_C_c : c ∉ C.fv) (dv_R_b : b ∉ R.fv)
    (dv_R_c : c ∉ R.fv) (dv_b_c : b ≠ c) :
    TAlphaWff [((nb083_alpha_dummy_000 A B C R), b)]
      (Wff.imp (Wff.classMem (Class.cv (nb083_alpha_dummy_000 A B C R)) A) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (nb083_alpha_dummy_000 A B C R)) (syn_csep2 B C))
            (syn_wral (nb083_alpha_dummy_001 A B C R) A (Wff.imp
                (Wff.classMem (Class.cv (nb083_alpha_dummy_001 A B C R)) (syn_csep2 B C))
                (syn_wbr (Class.cv (nb083_alpha_dummy_000 A B C R)) R
                  (Class.cv (nb083_alpha_dummy_001 A B C R))))))))
      (Wff.imp (Wff.classMem (Class.cv b) A) (Wff.neg
          (syn_wa (Wff.classMem (Class.cv b) (syn_csep2 B C)) (syn_wral c A
              (Wff.imp (Wff.classMem (Class.cv c) (syn_csep2 B C))
                (syn_wbr (Class.cv b) R (Class.cv c))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
      (TAlphaClass.refl_of_reflOn [((nb083_alpha_dummy_000 A B C R), b)] A
        (nb083_focused_refl_0000 A B C R b dv_A_b))) (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
          (TAlphaClass.refl_of_reflOn [((nb083_alpha_dummy_000 A B C R), b)]
            (syn_csep2 B C) (nb083_wpp_refl_0000 A B C R b dv_B_b dv_C_b))) (TAlphaWff.all
          (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn [((nb083_alpha_dummy_001 A B C R), c),
                  ((nb083_alpha_dummy_000 A B C R), b)]
                A (nb083_focused_refl_0001 A B C R b c dv_A_b dv_A_c))) (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_reflOn [((nb083_alpha_dummy_001 A B C R), c),
                    ((nb083_alpha_dummy_000 A B C R), b)] (syn_csep2 B C)
                  (nb083_wpp_refl_0001 A B C R b c dv_B_b dv_B_c dv_C_b dv_C_c)))
              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_003 A B C R)
        from (by
          unfold nb083_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  1)))) (show b ≠ (nb083_alpha_dummy_005 b c) from (by
          unfold nb083_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c) 1)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from (by
          unfold nb083_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  0)))) (show b ≠ (nb083_alpha_dummy_004 b c) from (by
          unfold nb083_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_000 A B C R) ≠
        (nb083_alpha_dummy_008 A B C R) from (by
          unfold nb083_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0004 A B C
                    R)
                  0)))) (show b ≠ (nb083_alpha_dummy_009 b c) from (by
          unfold nb083_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0005 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_000 A B C R) ≠
        (nb083_alpha_dummy_006 A B C R) from (by
          unfold nb083_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0001 A B
                    C R)
                  0)))) (show b ≠ (nb083_alpha_dummy_007 b c) from (by
          unfold nb083_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0003 b c)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv)
        (by decide)) dv_b_c (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_010 A B C R)
        from (by
          unfold nb083_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_012 b c) from (by
          unfold nb083_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_011 A B C R) from (by
          unfold nb083_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006
                    A B C R)
                  1)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_013 b c) from (by
          unfold nb083_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007
                    b c)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_005 b c))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010
        A B C R) ≠ (nb083_alpha_dummy_017 A B C R) from (by
          unfold
            nb083_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C
                    R)
                  1)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_020 b c) from (by
          unfold
            nb083_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  1)))) (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_016 A B C R) from (by
          unfold
            nb083_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B
                    C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_019 b c) from (by
          unfold
            nb083_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017
        A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R),
        (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015
        b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003
        A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R),
        (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009
        b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_c1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A
        B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_018 A
        B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠ (nb083_alpha_dummy_024 A B C R)
        from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_018 A
        B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017
        A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R),
        (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015
        b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003
        A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R),
        (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009
        b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_028 A B C R) from (by
          unfold
            nb083_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_029 b c) from (by
          unfold
            nb083_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A
        B C R) ≠ (nb083_alpha_dummy_028 A B C R) from (by
          unfold
            nb083_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_029 b c) from (by
          unfold
            nb083_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠ (nb083_alpha_dummy_030 A B C R)
        from (by
          unfold
            nb083_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_031 b c) from (by
          unfold
            nb083_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_018 A
        B C R) ≠ (nb083_alpha_dummy_030 A B C R) from (by
          unfold
            nb083_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_031 b c) from (by
          unfold
            nb083_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by
          simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by
          simp only [fv_syn_cnnc]))))))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_003 A B C R)
        from (by
          unfold nb083_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  1)))) (show b ≠ (nb083_alpha_dummy_005 b c) from (by
          unfold nb083_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c) 1)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_000 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from (by
          unfold nb083_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0000 A B C R)
                  0)))) (show b ≠ (nb083_alpha_dummy_004 b c) from (by
          unfold nb083_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0002 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_000 A B C R) ≠
        (nb083_alpha_dummy_008 A B C R) from (by
          unfold nb083_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0004 A B C
                    R)
                  0)))) (show b ≠ (nb083_alpha_dummy_009 b c) from (by
          unfold nb083_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0005 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_000 A B C R) ≠
        (nb083_alpha_dummy_006 A B C R) from (by
          unfold nb083_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0001 A B
                    C R)
                  0)))) (show b ≠ (nb083_alpha_dummy_007 b c) from (by
          unfold nb083_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0003 b c)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv)
        (by decide)) dv_b_c (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_010 A B C R)
        from (by
          unfold nb083_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_012 b c) from (by
          unfold nb083_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_011 A B C R) from (by
          unfold nb083_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006
                    A B C R)
                  1)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_013 b c) from (by
          unfold nb083_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007
                    b c)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_005 b c))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010
        A B C R) ≠ (nb083_alpha_dummy_017 A B C R) from (by
          unfold
            nb083_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C
                    R)
                  1)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_020 b c) from (by
          unfold
            nb083_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  1)))) (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_016 A B C R) from (by
          unfold
            nb083_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B
                    C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_019 b c) from (by
          unfold
            nb083_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0011
                    b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017
        A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R),
        (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015
        b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003
        A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R),
        (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009
        b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_c1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A
        B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_018 A
        B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠ (nb083_alpha_dummy_024 A B C R)
        from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0014
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0015
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0012
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0013
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_018 A
        B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
          unfold
            nb083_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0018
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_025 b c) from (by
          unfold
            nb083_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0019
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_022 A B C R) from (by
          unfold
            nb083_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0016
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_023 b c) from (by
          unfold
            nb083_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0017
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017
        A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R),
        (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015
        b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_003
        A B C R), (nb083_alpha_dummy_005 b c)), ((nb083_alpha_dummy_002 A B C R),
        (nb083_alpha_dummy_004 b c)), ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009
        b c)), ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_028 A B C R) from (by
          unfold
            nb083_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_029 b c) from (by
          unfold
            nb083_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A
        B C R) ≠ (nb083_alpha_dummy_028 A B C R) from (by
          unfold
            nb083_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0022
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_029 b c) from (by
          unfold
            nb083_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0023
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0020
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_020 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0021
                    b
                    c)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_010
        A B C R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠ (nb083_alpha_dummy_030 A B C R)
        from (by
          unfold
            nb083_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_031 b c) from (by
          unfold
            nb083_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_018 A
        B C R) ≠ (nb083_alpha_dummy_030 A B C R) from (by
          unfold
            nb083_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0026
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_031 b c) from (by
          unfold
            nb083_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0027
                    b
                    c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_018 A B C R) ≠
        (nb083_alpha_dummy_026 A B C R) from (by
          unfold
            nb083_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0024
                    A
                    B
                    C
                    R)
                  0)))) (show (nb083_alpha_dummy_021 b c) ≠ (nb083_alpha_dummy_027 b c) from (by
          unfold
            nb083_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0025
                    b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by
          simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold
            nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold
            nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009
                    b c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_008 A B C R), (nb083_alpha_dummy_009 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb083_split_alpha_0000 A B C R b c))))))))
                (TAlphaClass.refl_of_reflOn [((nb083_alpha_dummy_001 A B C R), c),
                    ((nb083_alpha_dummy_000 A B C R), b)]
                  R (nb083_focused_refl_0002 A B C R b c dv_R_b dv_R_c)))))))))

@[expose]
noncomputable def nominal_df_fpiv (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_C : Disjoint A.fv C.fv)
    (__dv_A_R : Disjoint A.fv R.fv) (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv)
    (__dv_B_C : Disjoint B.fv C.fv) (__dv_B_R : Disjoint B.fv R.fv) (dv_B_b : b ∉ B.fv)
    (dv_B_c : c ∉ B.fv) (__dv_C_R : Disjoint C.fv R.fv) (dv_C_b : b ∉ C.fv)
    (dv_C_c : c ∉ C.fv) (dv_R_b : b ∉ R.fv) (dv_R_c : c ∉ R.fv) (dv_b_c : b ≠ c) :
    Nominal.NPrf
      (.classEq (syn_cfpiv R A B C) (syn_crab b A (syn_wa (.classMem (.cv b) (syn_csep2 B C))
            (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C))
                (syn_wbr (.cv b) R (.cv c))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.neg
          (nb083_split_alpha_0001 A B C R b c dv_A_b dv_A_c dv_B_b dv_B_c dv_C_b dv_C_c
            dv_R_b dv_R_c dv_b_c)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
