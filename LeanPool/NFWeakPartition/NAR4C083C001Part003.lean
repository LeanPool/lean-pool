/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C083C001Part001

/-! NF weak partition development: NAR4C083C001Part003. -/


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
noncomputable def nb083_split_alpha_0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) :
    TAlphaWff
      [((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)]
      (Wff.imp (Wff.classMem (Class.cv (nb083_alpha_dummy_032 A B C R))
          (Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
              (Class.cv (nb083_alpha_dummy_001 A B C R))
              (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb083_alpha_dummy_032 A B C R))
            (Class.cab (nb083_alpha_dummy_002 A B C R) (syn_wrex (nb083_alpha_dummy_003 A B C R)
                (Class.cv (nb083_alpha_dummy_001 A B C R))
                (Wff.classEq (Class.cv (nb083_alpha_dummy_002 A B C R))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_003 A B C R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb083_alpha_dummy_033 b c))
          (Class.cab (nb083_alpha_dummy_004 b c)
            (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
              (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb083_alpha_dummy_033 b c))
            (Class.cab (nb083_alpha_dummy_004 b c)
              (syn_wrex (nb083_alpha_dummy_005 b c) (Class.cv c)
                (Wff.classEq (Class.cv (nb083_alpha_dummy_004 b c))
                  (syn_cun (syn_cphi (Class.cv (nb083_alpha_dummy_005 b c)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_003 A B C R) from
                    (by
                      unfold nb083_alpha_dummy_003;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 1))))
                  (show c ≠ (nb083_alpha_dummy_005 b c) from (by
                      unfold nb083_alpha_dummy_005;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb083_support_mem_0030 b c) 1)))) (TAlphaVar.there
                    (show (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from
                      (by
                        unfold nb083_alpha_dummy_002;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 0))))
                    (show c ≠ (nb083_alpha_dummy_004 b c) from (by
                        unfold nb083_alpha_dummy_004;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb083_support_mem_0030 b c) 0))))
                    (TAlphaVar.there (show
                        (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_032 A B C R) from
                        (by
                          unfold nb083_alpha_dummy_032;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb083_support_mem_0032 A B C R) 0))))
                      (show c ≠ (nb083_alpha_dummy_033 b c) from (by
                          unfold nb083_alpha_dummy_033;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb083_support_mem_0033 b c) 0))))
                      (TAlphaVar.there (show (nb083_alpha_dummy_001 A B C R) ≠
                            (nb083_alpha_dummy_006 A B C R) from (by
                            unfold nb083_alpha_dummy_006;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb083_support_mem_0029 A B C R) 0))))
                        (show c ≠ (nb083_alpha_dummy_007 b c) from (by
                            unfold nb083_alpha_dummy_007;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb083_support_mem_0031 b c) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
                      ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) (by decide))
                  (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_010 A B C R) from (by
          unfold nb083_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_012 b c) from (by
          unfold nb083_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c) 0)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_011 A B C R) from (by
          unfold nb083_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  1)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_013 b c) from (by
          unfold nb083_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c) 1)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_036 A B C R) from (by
          unfold nb083_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0036 A B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_037 b c) from (by
          unfold nb083_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0037 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_034 A B C R) from (by
          unfold nb083_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0034 A B C
                    R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_035 b c) from (by
          unfold nb083_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0035 b c)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_003 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb083_alpha_dummy_005 b c))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_017 A B C R) from (by
          unfold
            nb083_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C R)
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
                    A B C R)
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
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)),
        ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)),
        ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)),
        ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_c1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_017 A B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
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
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036
        A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R),
        (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005
        b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006
        A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c),
        ((nb083_alpha_dummy_000 A B C R), b)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
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
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b
                    c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A B
                    C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b
                    c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_010 A B C R) from (by
          unfold nb083_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_012 b c) from (by
          unfold nb083_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c) 0)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_011 A B C R) from (by
          unfold nb083_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  1)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_013 b c) from (by
          unfold nb083_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c) 1)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_036 A B C R) from (by
          unfold nb083_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0036 A B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_037 b c) from (by
          unfold nb083_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0037 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_034 A B C R) from (by
          unfold nb083_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0034 A B C
                    R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_035 b c) from (by
          unfold nb083_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0035 b c)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_003 A B C R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb083_alpha_dummy_005 b c))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_017 A B C R) from (by
          unfold
            nb083_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C R)
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
                    A B C R)
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
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)),
        ((nb083_alpha_dummy_017 A B C R), (nb083_alpha_dummy_020 b c)),
        ((nb083_alpha_dummy_016 A B C R), (nb083_alpha_dummy_019 b c)),
        ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_c1c)
        (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_017 A B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
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
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036
        A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R),
        (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005
        b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006
        A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c),
        ((nb083_alpha_dummy_000 A B C R), b)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_017 A B C R) ≠
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
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b
                    c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A B
                    C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b
                    c)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015 b c)),
        ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)),
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
                          ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
                          ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
                          ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
                          ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
                          ((nb083_alpha_dummy_001 A B C R), c),
                          ((nb083_alpha_dummy_000 A B C R), b)] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show
                      (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_003 A B C R) from (by
                        unfold nb083_alpha_dummy_003;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 1))))
                    (show c ≠ (nb083_alpha_dummy_005 b c) from (by
                        unfold nb083_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb083_support_mem_0030 b c) 1))))
                    (TAlphaVar.there (show
                        (nb083_alpha_dummy_001 A B C R) ≠ (nb083_alpha_dummy_002 A B C R) from
                        (by
                          unfold nb083_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb083_support_mem_0028 A B C R) 0))))
                      (show c ≠ (nb083_alpha_dummy_004 b c) from (by
                          unfold nb083_alpha_dummy_004;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb083_support_mem_0030 b c) 0))))
                      (TAlphaVar.there (show (nb083_alpha_dummy_001 A B C R) ≠
                            (nb083_alpha_dummy_032 A B C R) from (by
                            unfold nb083_alpha_dummy_032;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb083_support_mem_0032 A B C R) 0))))
                        (show c ≠ (nb083_alpha_dummy_033 b c) from (by
                            unfold nb083_alpha_dummy_033;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb083_support_mem_0033 b c) 0))))
                        (TAlphaVar.there (show (nb083_alpha_dummy_001 A B C R) ≠
                              (nb083_alpha_dummy_006 A B C R) from (by
                              unfold nb083_alpha_dummy_006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb083_support_mem_0029 A B C R)
                                      0)))) (show c ≠ (nb083_alpha_dummy_007 b c) from (by
                              unfold nb083_alpha_dummy_007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb083_support_mem_0031 b c) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb083_alpha_dummy_000 A B C R))).fv ∪
                        ((Class.cv (nb083_alpha_dummy_001 A B C R))).fv) (by decide))
                    (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv c)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_010 A B C R)
        from (by
          unfold nb083_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_012 b c) from (by
          unfold nb083_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c) 0)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_011 A B C R) from (by
          unfold nb083_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  1)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_013 b c) from (by
          unfold nb083_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c)
                  1)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_036 A B C R) from (by
          unfold nb083_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0036 A B C
                    R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_037 b c) from (by
          unfold nb083_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0037 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_034 A B C R) from (by
          unfold nb083_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0034 A B
                    C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_035 b c) from (by
          unfold nb083_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0035 b c)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_005 b c))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_017 A B C R) from (by
          unfold
            nb083_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C R)
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
                    A B C R)
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
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017
        A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R),
        (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015
        b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036
        A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R),
        (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005
        b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006
        A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c),
        ((nb083_alpha_dummy_000 A B C R), b)] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_017 A B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
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
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036
        A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R),
        (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005
        b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006
        A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c),
        ((nb083_alpha_dummy_000 A B C R), b)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
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
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
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
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_010 A B C R)
        from (by
          unfold nb083_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_012 b c) from (by
          unfold nb083_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c) 0)))) (TAlphaVar.there (show
        (nb083_alpha_dummy_003 A B C R) ≠ (nb083_alpha_dummy_011 A B C R) from (by
          unfold nb083_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0006 A B C R)
                  1)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_013 b c) from (by
          unfold nb083_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0007 b c)
                  1)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_036 A B C R) from (by
          unfold nb083_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0036 A B C
                    R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_037 b c) from (by
          unfold nb083_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0037 b c)
                  0)))) (TAlphaVar.there (show (nb083_alpha_dummy_003 A B C R) ≠
        (nb083_alpha_dummy_034 A B C R) from (by
          unfold nb083_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0034 A B
                    C R)
                  0)))) (show (nb083_alpha_dummy_005 b c) ≠ (nb083_alpha_dummy_035 b c) from (by
          unfold nb083_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0035 b c)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb083_alpha_dummy_003 A B C R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_005 b c))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_017 A B C R) from (by
          unfold
            nb083_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0010
                    A B C R)
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
                    A B C R)
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
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb083_alpha_dummy_018 A B C R), (nb083_alpha_dummy_021 b c)), ((nb083_alpha_dummy_017
        A B C R), (nb083_alpha_dummy_020 b c)), ((nb083_alpha_dummy_016 A B C R),
        (nb083_alpha_dummy_019 b c)), ((nb083_alpha_dummy_014 A B C R), (nb083_alpha_dummy_015
        b c)), ((nb083_alpha_dummy_010 A B C R), (nb083_alpha_dummy_012 b c)),
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036
        A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R),
        (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005
        b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006
        A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c),
        ((nb083_alpha_dummy_000 A B C R), b)] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_017 A B C R) ≠ (nb083_alpha_dummy_024 A B C R) from (by
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
        ((nb083_alpha_dummy_011 A B C R), (nb083_alpha_dummy_013 b c)), ((nb083_alpha_dummy_036
        A B C R), (nb083_alpha_dummy_037 b c)), ((nb083_alpha_dummy_034 A B C R),
        (nb083_alpha_dummy_035 b c)), ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005
        b c)), ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)), ((nb083_alpha_dummy_006
        A B C R), (nb083_alpha_dummy_007 b c)), ((nb083_alpha_dummy_001 A B C R), c),
        ((nb083_alpha_dummy_000 A B C R), b)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb083_alpha_dummy_010 A B C R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb083_alpha_dummy_012 b c))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
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
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb083_alpha_dummy_010 A B C R) ≠ (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008 A
                    B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0009 b
                    c)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb083_alpha_dummy_010 A B C R) ≠
        (nb083_alpha_dummy_014 A B C R) from (by
          unfold nb083_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb083_support_mem_0008
                    A B C R)
                  0)))) (show (nb083_alpha_dummy_012 b c) ≠ (nb083_alpha_dummy_015 b c) from (by
          unfold nb083_alpha_dummy_015;
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
        ((nb083_alpha_dummy_036 A B C R), (nb083_alpha_dummy_037 b c)),
        ((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
        ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
        ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
        ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
        ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
        ((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)] (syn_cnnc)
        (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb083_alpha_dummy_034 A B C R), (nb083_alpha_dummy_035 b c)),
                            ((nb083_alpha_dummy_003 A B C R), (nb083_alpha_dummy_005 b c)),
                            ((nb083_alpha_dummy_002 A B C R), (nb083_alpha_dummy_004 b c)),
                            ((nb083_alpha_dummy_032 A B C R), (nb083_alpha_dummy_033 b c)),
                            ((nb083_alpha_dummy_006 A B C R), (nb083_alpha_dummy_007 b c)),
                            ((nb083_alpha_dummy_001 A B C R), c),
                            ((nb083_alpha_dummy_000 A B C R), b)]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb083_focused_notmem_0006 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_001 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb083_focused_notmem_0007 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb083_alpha_dummy_000 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb083_compact_envfresh_0011 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_R_b : b ∉ R.fv) (dv_R_c : c ∉ R.fv) :
    TEnvFresh [((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb083_alpha_dummy_001 A B C R) c
      (nb083_focused_notmem_0006 A B C R) dv_R_c
      (TEnvFresh.consFresh (nb083_alpha_dummy_000 A B C R) b
        (nb083_focused_notmem_0007 A B C R) dv_R_b (TEnvFresh.nil R.fv)))

@[expose]
noncomputable def nb083_focused_refl_0002 (A : Class) (B : Class) (C : Class) (R : Class)
    (b : Var) (c : Var) (dv_R_b : b ∉ R.fv) (dv_R_c : c ∉ R.fv) :
    TReflOn [((nb083_alpha_dummy_001 A B C R), c), ((nb083_alpha_dummy_000 A B C R), b)]
      R.fv :=
  TEnvFresh.reflOn (nb083_compact_envfresh_0011 A B C R b c dv_R_b dv_R_c)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
