/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C072C001Block001

/-! NF weak partition development: NAR4C072C001Part007. -/


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
noncomputable def nb072_split_alpha_0000 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) :
    TAlphaWff
      [((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_032 A B R S_cls H))
          (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
            (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
              (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
              (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_032 A B R S_cls H))
            (Class.cab (nb072_alpha_dummy_002 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_003 A B R S_cls H)
                (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_002 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_003 A B R S_cls H)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_033 x y))
          (Class.cab (nb072_alpha_dummy_004 x y)
            (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_033 x y))
            (Class.cab (nb072_alpha_dummy_004 x y)
              (syn_wrex (nb072_alpha_dummy_005 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb072_alpha_dummy_004 x y))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_005 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                      (nb072_alpha_dummy_003 A B R S_cls H) from (by
                      unfold nb072_alpha_dummy_003;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H) 1))))
                  (show y ≠ (nb072_alpha_dummy_005 x y) from (by
                      unfold nb072_alpha_dummy_005;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0030 x y) 1)))) (TAlphaVar.there
                    (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                        (nb072_alpha_dummy_002 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_002;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H)
                                0)))) (show y ≠ (nb072_alpha_dummy_004 x y) from (by
                        unfold nb072_alpha_dummy_004;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                          (nb072_alpha_dummy_032 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_032;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0032 A B R S_cls H)
                                  0)))) (show y ≠ (nb072_alpha_dummy_033 x y) from (by
                          unfold nb072_alpha_dummy_033;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0033 x y) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                            (nb072_alpha_dummy_006 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_006;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0029 A B R S_cls H)
                                    0)))) (show y ≠ (nb072_alpha_dummy_007 x y) from (by
                            unfold nb072_alpha_dummy_007;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0031 x y) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
                      ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_010 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_012 x y) from (by
          unfold nb072_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_011 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_013 x y) from (by
          unfold nb072_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_036 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_037 x y) from (by
          unfold nb072_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_034 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_035 x y) from (by
          unfold nb072_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_003 A B R S_cls H))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_017 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_020 x y) from (by
          unfold
            nb072_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_016 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_019 x y) from (by
          unfold
            nb072_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold
            nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012
        x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A
        B R S_cls H) ≠ (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠ (nb072_alpha_dummy_030 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_030 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A B
                    R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_010 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_012 x y) from (by
          unfold nb072_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_011 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_013 x y) from (by
          unfold nb072_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_036 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_037 x y) from (by
          unfold nb072_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_034 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_035 x y) from (by
          unfold nb072_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_003 A B R S_cls H))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_017 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_020 x y) from (by
          unfold
            nb072_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_016 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_019 x y) from (by
          unfold
            nb072_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold
            nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012
        x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A
        B R S_cls H) ≠ (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠ (nb072_alpha_dummy_030 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_030 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A B
                    R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed [((nb072_alpha_dummy_034 A B R S_cls H),
                            (nb072_alpha_dummy_035 x y)),
                          ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
                          ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
                          ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
                          ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
                          ((nb072_alpha_dummy_001 A B R S_cls H), y),
                          ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                        (nb072_alpha_dummy_003 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_003;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H)
                                1)))) (show y ≠ (nb072_alpha_dummy_005 x y) from (by
                        unfold nb072_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0030 x y) 1))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                          (nb072_alpha_dummy_002 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0028 A B R S_cls H)
                                  0)))) (show y ≠ (nb072_alpha_dummy_004 x y) from (by
                          unfold nb072_alpha_dummy_004;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0030 x y) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                            (nb072_alpha_dummy_032 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_032;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0032 A B R S_cls H)
                                    0)))) (show y ≠ (nb072_alpha_dummy_033 x y) from (by
                            unfold nb072_alpha_dummy_033;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0033 x y) 0))))
                        (TAlphaVar.there (show (nb072_alpha_dummy_001 A B R S_cls H) ≠
                              (nb072_alpha_dummy_006 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_006;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0029 A B R S_cls H) 0))))
                          (show y ≠ (nb072_alpha_dummy_007 x y) from (by
                              unfold nb072_alpha_dummy_007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0031 x y) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪
                        ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_010 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_012 x y) from (by
          unfold nb072_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_011 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_013 x y) from (by
          unfold nb072_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_036 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_037 x y) from (by
          unfold nb072_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_034 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B
                    R S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_035 x y) from (by
          unfold nb072_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls
        H))).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_017 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_020 x y) from (by
          unfold
            nb072_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_016 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_019 x y) from (by
          unfold
            nb072_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold
            nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012
        x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A
        B R S_cls H) ≠ (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠ (nb072_alpha_dummy_030 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_030 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_010 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_012 x y) from (by
          unfold nb072_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_003 A B R S_cls H) ≠ (nb072_alpha_dummy_011 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0006 A B R
                    S_cls H)
                  1)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_013 x y) from (by
          unfold nb072_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0007 x y)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_036 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0036 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_037 x y) from (by
          unfold nb072_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0037 x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_003 A B R S_cls H) ≠
        (nb072_alpha_dummy_034 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0034 A B
                    R S_cls H)
                  0)))) (show (nb072_alpha_dummy_005 x y) ≠ (nb072_alpha_dummy_035 x y) from (by
          unfold nb072_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0035 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls
        H))).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_017 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_020 x y) from (by
          unfold
            nb072_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_016 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0010
                    A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_019 x y) from (by
          unfold
            nb072_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold
            nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠ (nb072_alpha_dummy_024 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0014
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0015
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0012
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0013
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_024 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0018
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_025 x y) from (by
          unfold
            nb072_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_022 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0016
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_023 x y) from (by
          unfold
            nb072_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_018 A B R S_cls H), (nb072_alpha_dummy_021 x y)),
        ((nb072_alpha_dummy_017 A B R S_cls H), (nb072_alpha_dummy_020 x y)),
        ((nb072_alpha_dummy_016 A B R S_cls H), (nb072_alpha_dummy_019 x y)),
        ((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012
        x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_010 A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_017 A
        B R S_cls H) ≠ (nb072_alpha_dummy_028 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0022
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_029 x y) from (by
          unfold
            nb072_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_017 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0020
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_020 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_010
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_012 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠ (nb072_alpha_dummy_030 A
        B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_018 A
        B R S_cls H) ≠ (nb072_alpha_dummy_030 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0026
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_031 x y) from (by
          unfold
            nb072_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_018 A B R S_cls H) ≠
        (nb072_alpha_dummy_026 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0024
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_021 x y) ≠ (nb072_alpha_dummy_027 x y) from (by
          unfold
            nb072_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_010 A B R S_cls H) ≠ (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_010 A B R S_cls H) ≠
        (nb072_alpha_dummy_014 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0008
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_012 x y) ≠ (nb072_alpha_dummy_015 x y) from (by
          unfold nb072_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_014 A B R S_cls H), (nb072_alpha_dummy_015 x y)),
        ((nb072_alpha_dummy_010 A B R S_cls H), (nb072_alpha_dummy_012 x y)),
        ((nb072_alpha_dummy_011 A B R S_cls H), (nb072_alpha_dummy_013 x y)),
        ((nb072_alpha_dummy_036 A B R S_cls H), (nb072_alpha_dummy_037 x y)),
        ((nb072_alpha_dummy_034 A B R S_cls H), (nb072_alpha_dummy_035 x y)),
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_032 A B R S_cls H), (nb072_alpha_dummy_033 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed [((nb072_alpha_dummy_034 A B R S_cls H),
                              (nb072_alpha_dummy_035 x y)),
                            ((nb072_alpha_dummy_003 A B R S_cls H),
                              (nb072_alpha_dummy_005 x y)),
                            ((nb072_alpha_dummy_002 A B R S_cls H),
                              (nb072_alpha_dummy_004 x y)),
                            ((nb072_alpha_dummy_032 A B R S_cls H),
                              (nb072_alpha_dummy_033 x y)),
                            ((nb072_alpha_dummy_006 A B R S_cls H),
                              (nb072_alpha_dummy_007 x y)),
                            ((nb072_alpha_dummy_001 A B R S_cls H), y),
                            ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb072_focused_notmem_0002 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∉ R.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))

theorem nb072_focused_notmem_0003 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∉ R.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))

theorem nb072_compact_envfresh_0010 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TEnvFresh
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y
      (nb072_focused_notmem_0002 A B R S_cls H) dv_R_y
      (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x
        (nb072_focused_notmem_0003 A B R S_cls H) dv_R_x (TEnvFresh.nil R.fv)))

@[expose]
noncomputable def nb072_focused_refl_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TReflOn
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      R.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0010 x y A B R S_cls H dv_R_x dv_R_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
