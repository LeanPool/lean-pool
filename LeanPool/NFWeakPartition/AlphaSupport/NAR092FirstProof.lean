/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C092M3Part001

/-! NF weak partition development: NAR4H5C092M3Part002. -/


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
noncomputable def nb092_split_alpha_0000 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb092_alpha_dummy_036 R), (nb092_alpha_dummy_037 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb092_alpha_dummy_036 R))
          (Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb092_alpha_dummy_036 R))
            (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb092_alpha_dummy_037 a b))
          (Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb092_alpha_dummy_037 a b))
            (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_007 R) from (by
                      unfold nb092_alpha_dummy_007;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 1))))
                  (show b ≠ (nb092_alpha_dummy_009 a b) from (by
                      unfold nb092_alpha_dummy_009;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb092_support_mem_0034 a b) 1)))) (TAlphaVar.there
                    (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_006 R) from (by
                        unfold nb092_alpha_dummy_006;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb092_support_mem_0032 R) 0))))
                    (show b ≠ (nb092_alpha_dummy_008 a b) from (by
                        unfold nb092_alpha_dummy_008;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb092_support_mem_0034 a b) 0))))
                    (TAlphaVar.there
                      (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_036 R) from (by
                          unfold nb092_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb092_support_mem_0036 R) 0))))
                      (show b ≠ (nb092_alpha_dummy_037 a b) from (by
                          unfold nb092_alpha_dummy_037;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb092_support_mem_0037 a b) 0))))
                      (TAlphaVar.there
                        (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_010 R) from (by
                            unfold nb092_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb092_support_mem_0033 R) 0))))
                        (show b ≠ (nb092_alpha_dummy_011 a b) from (by
                            unfold nb092_alpha_dummy_011;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb092_support_mem_0035 a b) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪
                      ((Class.cv (nb092_alpha_dummy_001 R))).fv) (by decide))
                  (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_014 R) from (by
          unfold nb092_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 0)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_016 a b) from (by
          unfold nb092_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 0)))) (TAlphaVar.there (show
        (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_015 R) from (by
          unfold nb092_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 1)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_017 a b) from (by
          unfold nb092_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 1)))) (TAlphaVar.there (show
        (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_040 R) from (by
          unfold nb092_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0040 R) 0)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_041 a b) from (by
          unfold nb092_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0041 a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_038 R) from (by
          unfold nb092_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0038 R)
                  0)))) (show (nb092_alpha_dummy_009 a b) ≠ (nb092_alpha_dummy_039 a b) from (by
          unfold nb092_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0039 a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_007 R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_009 a b))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_014 R) ≠ (nb092_alpha_dummy_021 R) from (by
          unfold
            nb092_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  1)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_024 a b) from (by
          unfold
            nb092_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  1)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_020 R) from (by
          unfold
            nb092_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_023 a b) from (by
          unfold
            nb092_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold
            nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold
            nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021
        R) ≠ (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_014 R) ≠ (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_014 R) from (by
          unfold nb092_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 0)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_016 a b) from (by
          unfold nb092_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 0)))) (TAlphaVar.there (show
        (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_015 R) from (by
          unfold nb092_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 1)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_017 a b) from (by
          unfold nb092_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 1)))) (TAlphaVar.there (show
        (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_040 R) from (by
          unfold nb092_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0040 R) 0)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_041 a b) from (by
          unfold nb092_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0041 a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_038 R) from (by
          unfold nb092_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0038 R)
                  0)))) (show (nb092_alpha_dummy_009 a b) ≠ (nb092_alpha_dummy_039 a b) from (by
          unfold nb092_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0039 a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_007 R))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_009 a b))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_014 R) ≠ (nb092_alpha_dummy_021 R) from (by
          unfold
            nb092_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  1)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_024 a b) from (by
          unfold
            nb092_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  1)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_020 R) from (by
          unfold
            nb092_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_023 a b) from (by
          unfold
            nb092_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold
            nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold
            nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021
        R) ≠ (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_014 R) ≠ (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb092_alpha_dummy_038 R), (nb092_alpha_dummy_039 a b)),
                          ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
                          ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)),
                          ((nb092_alpha_dummy_036 R), (nb092_alpha_dummy_037 a b)),
                          ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
                          ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
                          ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_007 R) from (by
                        unfold nb092_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb092_support_mem_0032 R) 1))))
                    (show b ≠ (nb092_alpha_dummy_009 a b) from (by
                        unfold nb092_alpha_dummy_009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb092_support_mem_0034 a b) 1))))
                    (TAlphaVar.there
                      (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_006 R) from (by
                          unfold nb092_alpha_dummy_006;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb092_support_mem_0032 R) 0))))
                      (show b ≠ (nb092_alpha_dummy_008 a b) from (by
                          unfold nb092_alpha_dummy_008;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb092_support_mem_0034 a b) 0))))
                      (TAlphaVar.there
                        (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_036 R) from (by
                            unfold nb092_alpha_dummy_036;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb092_support_mem_0036 R) 0))))
                        (show b ≠ (nb092_alpha_dummy_037 a b) from (by
                            unfold nb092_alpha_dummy_037;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb092_support_mem_0037 a b) 0))))
                        (TAlphaVar.there
                          (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_010 R) from (by
                              unfold nb092_alpha_dummy_010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb092_support_mem_0033 R) 0))))
                          (show b ≠ (nb092_alpha_dummy_011 a b) from (by
                              unfold nb092_alpha_dummy_011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb092_support_mem_0035 a b) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪
                        ((Class.cv (nb092_alpha_dummy_001 R))).fv) (by decide))
                    (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_014 R) from (by
          unfold nb092_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 0)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_016 a b) from (by
          unfold nb092_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 0)))) (TAlphaVar.there (show
        (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_015 R) from (by
          unfold nb092_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 1)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_017 a b) from (by
          unfold nb092_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b)
                  1)))) (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_040 R) from (by
          unfold nb092_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0040 R)
                  0)))) (show (nb092_alpha_dummy_009 a b) ≠ (nb092_alpha_dummy_041 a b) from (by
          unfold nb092_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0041 a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_038 R) from (by
          unfold nb092_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0038 R)
                  0)))) (show (nb092_alpha_dummy_009 a b) ≠ (nb092_alpha_dummy_039 a b) from (by
          unfold nb092_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0039 a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_007 R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_009 a b))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014
        R) ≠ (nb092_alpha_dummy_021 R) from (by
          unfold
            nb092_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  1)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_024 a b) from (by
          unfold
            nb092_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  1)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_020 R) from (by
          unfold
            nb092_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_023 a b) from (by
          unfold
            nb092_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold
            nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold
            nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021
        R) ≠ (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_014 R) ≠ (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_014 R) from (by
          unfold nb092_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 0)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_016 a b) from (by
          unfold nb092_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b) 0)))) (TAlphaVar.there (show
        (nb092_alpha_dummy_007 R) ≠ (nb092_alpha_dummy_015 R) from (by
          unfold nb092_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0010 R) 1)))) (show (nb092_alpha_dummy_009 a b) ≠
        (nb092_alpha_dummy_017 a b) from (by
          unfold nb092_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0011 a b)
                  1)))) (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_040 R) from (by
          unfold nb092_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0040 R)
                  0)))) (show (nb092_alpha_dummy_009 a b) ≠ (nb092_alpha_dummy_041 a b) from (by
          unfold nb092_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0041 a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_007 R) ≠
        (nb092_alpha_dummy_038 R) from (by
          unfold nb092_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0038 R)
                  0)))) (show (nb092_alpha_dummy_009 a b) ≠ (nb092_alpha_dummy_039 a b) from (by
          unfold nb092_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0039 a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_007 R))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_009 a b))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014
        R) ≠ (nb092_alpha_dummy_021 R) from (by
          unfold
            nb092_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  1)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_024 a b) from (by
          unfold
            nb092_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  1)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_020 R) from (by
          unfold
            nb092_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0014
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_023 a b) from (by
          unfold
            nb092_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0015
                    a b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold
            nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold
            nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0018
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0019
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0016
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0017
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_028 R) from (by
          unfold
            nb092_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0022
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_029 a b) from (by
          unfold
            nb092_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0023
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_026 R) from (by
          unfold
            nb092_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0020
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_027 a b) from (by
          unfold
            nb092_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0021
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_022 R), (nb092_alpha_dummy_025 a b)), ((nb092_alpha_dummy_021 R),
        (nb092_alpha_dummy_024 a b)), ((nb092_alpha_dummy_020 R), (nb092_alpha_dummy_023 a b)),
        ((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004
        R), (nb092_alpha_dummy_005 x y R a b))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_021
        R) ≠ (nb092_alpha_dummy_032 R) from (by
          unfold
            nb092_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0026
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_033 a b) from (by
          unfold
            nb092_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0027
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_021 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0024
                    R)
                  0)))) (show (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0025
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092_alpha_dummy_014
        R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_022
        R) ≠ (nb092_alpha_dummy_034 R) from (by
          unfold
            nb092_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0030
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_035 a b) from (by
          unfold
            nb092_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0031
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb092_alpha_dummy_022 R) ≠
        (nb092_alpha_dummy_030 R) from (by
          unfold
            nb092_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0028
                    R)
                  0)))) (show (nb092_alpha_dummy_025 a b) ≠ (nb092_alpha_dummy_031 a b) from (by
          unfold
            nb092_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0029
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092_alpha_dummy_014 R) ≠ (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012 R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013 a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092_alpha_dummy_014 R) ≠
        (nb092_alpha_dummy_018 R) from (by
          unfold nb092_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0012
                    R)
                  0)))) (show (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_019 a b) from (by
          unfold nb092_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0013
                    a b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb092_alpha_dummy_018 R), (nb092_alpha_dummy_019 a b)), ((nb092_alpha_dummy_014 R),
        (nb092_alpha_dummy_016 a b)), ((nb092_alpha_dummy_015 R), (nb092_alpha_dummy_017 a b)),
        ((nb092_alpha_dummy_040 R), (nb092_alpha_dummy_041 a b)), ((nb092_alpha_dummy_038 R),
        (nb092_alpha_dummy_039 a b)), ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
        ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_036 R),
        (nb092_alpha_dummy_037 a b)), ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb092_alpha_dummy_038 R), (nb092_alpha_dummy_039 a b)),
                            ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)),
                            ((nb092_alpha_dummy_006 R), (nb092_alpha_dummy_008 a b)),
                            ((nb092_alpha_dummy_036 R), (nb092_alpha_dummy_037 a b)),
                            ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
                            ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
                            ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
