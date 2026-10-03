/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C081C001Block001

/-! NF weak partition development: NAR4C081C001Part004. -/


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
noncomputable def nb081_split_alpha_0000 (x : Var) (y : Var) (A : Class) :
    TAlphaWff
      [((nb081_alpha_dummy_034 A), (nb081_alpha_dummy_035 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))]
      (Wff.imp (Wff.classMem (Class.cv (nb081_alpha_dummy_034 A))
          (Class.cab (nb081_alpha_dummy_004 A)
            (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb081_alpha_dummy_034 A))
            (Class.cab (nb081_alpha_dummy_004 A)
              (syn_wrex (nb081_alpha_dummy_005 A) (Class.cv (nb081_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb081_alpha_dummy_004 A))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_005 A)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb081_alpha_dummy_035 x y))
          (Class.cab (nb081_alpha_dummy_006 x y)
            (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb081_alpha_dummy_035 x y))
            (Class.cab (nb081_alpha_dummy_006 x y)
              (syn_wrex (nb081_alpha_dummy_007 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb081_alpha_dummy_006 x y))
                  (syn_cun (syn_cphi (Class.cv (nb081_alpha_dummy_007 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_005 A) from (by
                      unfold nb081_alpha_dummy_005;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
                  (show y ≠ (nb081_alpha_dummy_007 x y) from (by
                      unfold nb081_alpha_dummy_007;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb081_support_mem_0034 x y) 1)))) (TAlphaVar.there
                    (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_004 A) from (by
                        unfold nb081_alpha_dummy_004;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
                    (show y ≠ (nb081_alpha_dummy_006 x y) from (by
                        unfold nb081_alpha_dummy_006;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
                    (TAlphaVar.there
                      (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_034 A) from (by
                          unfold nb081_alpha_dummy_034;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0036 A) 0))))
                      (show y ≠ (nb081_alpha_dummy_035 x y) from (by
                          unfold nb081_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0037 x y) 0))))
                      (TAlphaVar.there
                        (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_008 A) from (by
                            unfold nb081_alpha_dummy_008;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0033 A) 0))))
                        (show y ≠ (nb081_alpha_dummy_009 x y) from (by
                            unfold nb081_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0035 x y) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪
                      ((Class.cv (nb081_alpha_dummy_001 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_012 A) from (by
          unfold nb081_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_014 x y) from (by
          unfold nb081_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_013 A) from (by
          unfold nb081_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_015 x y) from (by
          unfold nb081_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_038 A) from (by
          unfold nb081_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_039 x y) from (by
          unfold nb081_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_036 A) from (by
          unfold nb081_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081_alpha_dummy_007 x y) ≠ (nb081_alpha_dummy_037 x y) from (by
          unfold nb081_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_005 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_007 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_019 A) from (by
          unfold
            nb081_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_022 x y) from (by
          unfold
            nb081_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_018 A) from (by
          unfold
            nb081_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_021 x y) from (by
          unfold
            nb081_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold
            nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold
            nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019
        A) ≠ (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_012 A) from (by
          unfold nb081_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_014 x y) from (by
          unfold nb081_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_013 A) from (by
          unfold nb081_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_015 x y) from (by
          unfold nb081_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_038 A) from (by
          unfold nb081_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_039 x y) from (by
          unfold nb081_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_036 A) from (by
          unfold nb081_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081_alpha_dummy_007 x y) ≠ (nb081_alpha_dummy_037 x y) from (by
          unfold nb081_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_005 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_007 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_019 A) from (by
          unfold
            nb081_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_022 x y) from (by
          unfold
            nb081_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_018 A) from (by
          unfold
            nb081_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_021 x y) from (by
          unfold
            nb081_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold
            nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold
            nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019
        A) ≠ (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb081_alpha_dummy_036 A), (nb081_alpha_dummy_037 x y)),
                          ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
                          ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)),
                          ((nb081_alpha_dummy_034 A), (nb081_alpha_dummy_035 x y)),
                          ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
                          ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
                          ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_005 A) from (by
                        unfold nb081_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0032 A) 1))))
                    (show y ≠ (nb081_alpha_dummy_007 x y) from (by
                        unfold nb081_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb081_support_mem_0034 x y) 1))))
                    (TAlphaVar.there
                      (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_004 A) from (by
                          unfold nb081_alpha_dummy_004;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0032 A) 0))))
                      (show y ≠ (nb081_alpha_dummy_006 x y) from (by
                          unfold nb081_alpha_dummy_006;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb081_support_mem_0034 x y) 0))))
                      (TAlphaVar.there
                        (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_034 A) from (by
                            unfold nb081_alpha_dummy_034;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0036 A) 0))))
                        (show y ≠ (nb081_alpha_dummy_035 x y) from (by
                            unfold nb081_alpha_dummy_035;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb081_support_mem_0037 x y) 0))))
                        (TAlphaVar.there
                          (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_008 A) from (by
                              unfold nb081_alpha_dummy_008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb081_support_mem_0033 A) 0))))
                          (show y ≠ (nb081_alpha_dummy_009 x y) from (by
                              unfold nb081_alpha_dummy_009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb081_support_mem_0035 x y) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪
                        ((Class.cv (nb081_alpha_dummy_001 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_012 A) from (by
          unfold nb081_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_014 x y) from (by
          unfold nb081_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_013 A) from (by
          unfold nb081_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_015 x y) from (by
          unfold nb081_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_038 A) from (by
          unfold nb081_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A)
                  0)))) (show (nb081_alpha_dummy_007 x y) ≠ (nb081_alpha_dummy_039 x y) from (by
          unfold nb081_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_036 A) from (by
          unfold nb081_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081_alpha_dummy_007 x y) ≠ (nb081_alpha_dummy_037 x y) from (by
          unfold nb081_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_005 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_007 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012
        A) ≠ (nb081_alpha_dummy_019 A) from (by
          unfold
            nb081_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_022 x y) from (by
          unfold
            nb081_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_018 A) from (by
          unfold
            nb081_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_021 x y) from (by
          unfold
            nb081_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold
            nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold
            nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019
        A) ≠ (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_012 A) from (by
          unfold nb081_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_014 x y) from (by
          unfold nb081_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_013 A) from (by
          unfold nb081_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_015 x y) from (by
          unfold nb081_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_038 A) from (by
          unfold nb081_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0040 A)
                  0)))) (show (nb081_alpha_dummy_007 x y) ≠ (nb081_alpha_dummy_039 x y) from (by
          unfold nb081_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0041 x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_036 A) from (by
          unfold nb081_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0038 A)
                  0)))) (show (nb081_alpha_dummy_007 x y) ≠ (nb081_alpha_dummy_037 x y) from (by
          unfold nb081_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0039 x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_005 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_007 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012
        A) ≠ (nb081_alpha_dummy_019 A) from (by
          unfold
            nb081_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_022 x y) from (by
          unfold
            nb081_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_018 A) from (by
          unfold
            nb081_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_021 x y) from (by
          unfold
            nb081_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold
            nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold
            nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002
        A), (nb081_alpha_dummy_003 x y A))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019
        A) ≠ (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_038 A), (nb081_alpha_dummy_039 x y)), ((nb081_alpha_dummy_036 A),
        (nb081_alpha_dummy_037 x y)), ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
        ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_034 A),
        (nb081_alpha_dummy_035 x y)), ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb081_alpha_dummy_036 A), (nb081_alpha_dummy_037 x y)),
                            ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)),
                            ((nb081_alpha_dummy_004 A), (nb081_alpha_dummy_006 x y)),
                            ((nb081_alpha_dummy_034 A), (nb081_alpha_dummy_035 x y)),
                            ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
                            ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
                            ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb081_focused_notmem_0000 (A : Class) : (nb081_alpha_dummy_001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

theorem nb081_focused_notmem_0001 (A : Class) : (nb081_alpha_dummy_000 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => hu)

theorem nb081_focused_notmem_0002 (A : Class) : (nb081_alpha_dummy_002 A) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb081_alpha_dummy_000 A)} : Finset Var) ∪
            ({(nb081_alpha_dummy_001 A)} : Finset Var) ∪ ((Wff.classMem
              (syn_copk (Class.cv (nb081_alpha_dummy_000 A))
                (Class.cv (nb081_alpha_dummy_001 A))) A)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_wff_classMem
      (syn_copk (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A)))
      A]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb081_focused_notmem_0003 (x : Var) (y : Var) (A : Class) :
    (nb081_alpha_dummy_003 x y A) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ((Wff.classMem (syn_copk (Class.cv x) (Class.cv y)) A)).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_wff_classMem (syn_copk (Class.cv x) (Class.cv y)) A]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb081_compact_envfresh_0007 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) :
    TEnvFresh
      [((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))]
      A.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb081_alpha_dummy_001 A) y (nb081_focused_notmem_0000 A) dv_A_y
      (TEnvFresh.consFresh (nb081_alpha_dummy_000 A) x (nb081_focused_notmem_0001 A) dv_A_x
        (TEnvFresh.consFresh (nb081_alpha_dummy_002 A) (nb081_alpha_dummy_003 x y A)
          (nb081_focused_notmem_0002 A) (nb081_focused_notmem_0003 x y A)
          (TEnvFresh.nil A.fv))))

@[expose]
noncomputable def nb081_focused_refl_0000 (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn
      [((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))]
      A.fv :=
  TEnvFresh.reflOn (nb081_compact_envfresh_0007 x y A dv_A_x dv_A_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
