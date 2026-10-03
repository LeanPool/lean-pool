/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C092M3Part002

/-! NF weak partition development: NAR4H5C092M3Part003. -/


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
noncomputable def nb092_split_alpha_0003 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) (dv_R_a : a ∉ R.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_a_b : a ≠ b) (dv_a_x : a ≠ x) (dv_b_x : b ≠ x)
    (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))]
      (Wff.imp (Wff.classEq (Class.cv (nb092_alpha_dummy_004 R))
          (syn_cop (Class.cv (nb092_alpha_dummy_000 R)) (Class.cv (nb092_alpha_dummy_001 R))))
        (Wff.neg (syn_wrex (nb092_alpha_dummy_002 R) (Class.cv (nb092_alpha_dummy_000 R))
            (syn_wrex (nb092_alpha_dummy_003 R) (Class.cv (nb092_alpha_dummy_001 R))
              (syn_wbr (Class.cv (nb092_alpha_dummy_002 R)) R
                (Class.cv (nb092_alpha_dummy_003 R)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb092_alpha_dummy_005 x y R a b))
          (syn_cop (Class.cv a) (Class.cv b))) (Wff.neg (syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wbr (Class.cv x) R (Class.cv y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_004 R) from (by
                unfold nb092_alpha_dummy_004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0002 R) 0)))))
          (Ne.symm (show b ≠ (nb092_alpha_dummy_005 x y R a b) from (by
                unfold nb092_alpha_dummy_005;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb092_support_mem_0003 x y R a b) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_004 R) from (by
                  unfold nb092_alpha_dummy_004;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0000 R) 0)))))
            (Ne.symm (show a ≠ (nb092_alpha_dummy_005 x y R a b) from (by
                  unfold nb092_alpha_dummy_005;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb092_support_mem_0001 x y R a b) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_007 R) from
                                    (by
                                      unfold nb092_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0004 R)
                                              1)))) (show a ≠ (nb092_alpha_dummy_009 a b) from
                                    (by
                                      unfold nb092_alpha_dummy_009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0006 a b)
                                              1)))) (TAlphaVar.there (show
                                      (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_006 R) from
                                      (by
                                        unfold nb092_alpha_dummy_006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0004 R)
                                                0)))) (show a ≠ (nb092_alpha_dummy_008 a b) from
                                      (by
                                        unfold nb092_alpha_dummy_008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0006 a b) 0))))
                                    (TAlphaVar.there (show (nb092_alpha_dummy_000 R) ≠
        (nb092_alpha_dummy_012 R) from (by
                                          unfold nb092_alpha_dummy_012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0008 R) 0))))
                                      (show a ≠ (nb092_alpha_dummy_013 a b) from (by
                                          unfold nb092_alpha_dummy_013;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0009 a b) 0))))
                                      (TAlphaVar.there (show (nb092_alpha_dummy_000 R) ≠
        (nb092_alpha_dummy_010 R) from (by
          unfold nb092_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0005 R) 0)))) (show a ≠ (nb092_alpha_dummy_011 a b) from
        (by
          unfold nb092_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0007 a b) 0)))) (TAlphaVar.there
        (freshVar_injective ((R).fv) (by decide)) dv_a_b (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪
                                      ((Class.cv (nb092_alpha_dummy_001 R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb092_support_mem_0011 a b) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_007 R))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_009 a b))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)), ((nb092_alpha_dummy_001 R),
        b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x
        y R a b))] (syn_c1c) (by
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)), ((nb092_alpha_dummy_001 R),
        b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005
        x y R a b))] (syn_c0) (by
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_007 R) from
                                    (by
                                      unfold nb092_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0004 R)
                                              1)))) (show a ≠ (nb092_alpha_dummy_009 a b) from
                                    (by
                                      unfold nb092_alpha_dummy_009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0006 a b)
                                              1)))) (TAlphaVar.there (show
                                      (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_006 R) from
                                      (by
                                        unfold nb092_alpha_dummy_006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0004 R)
                                                0)))) (show a ≠ (nb092_alpha_dummy_008 a b) from
                                      (by
                                        unfold nb092_alpha_dummy_008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0006 a b) 0))))
                                    (TAlphaVar.there (show (nb092_alpha_dummy_000 R) ≠
        (nb092_alpha_dummy_012 R) from (by
                                          unfold nb092_alpha_dummy_012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0008 R) 0))))
                                      (show a ≠ (nb092_alpha_dummy_013 a b) from (by
                                          unfold nb092_alpha_dummy_013;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0009 a b) 0))))
                                      (TAlphaVar.there (show (nb092_alpha_dummy_000 R) ≠
        (nb092_alpha_dummy_010 R) from (by
          unfold nb092_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0005 R) 0)))) (show a ≠ (nb092_alpha_dummy_011 a b) from
        (by
          unfold nb092_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0007 a b) 0)))) (TAlphaVar.there
        (freshVar_injective ((R).fv) (by decide)) dv_a_b (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪
                                      ((Class.cv (nb092_alpha_dummy_001 R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb092_support_mem_0011 a b) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_007 R))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb092_alpha_dummy_009 a b))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)), ((nb092_alpha_dummy_001 R),
        b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x
        y R a b))] (syn_c1c) (by
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)), ((nb092_alpha_dummy_001 R),
        b), ((nb092_alpha_dummy_000 R), a), ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005
        x y R a b))] (syn_c0) (by
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
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
        ((nb092_alpha_dummy_007 R), (nb092_alpha_dummy_009 a b)), ((nb092_alpha_dummy_006 R),
        (nb092_alpha_dummy_008 a b)), ((nb092_alpha_dummy_012 R), (nb092_alpha_dummy_013 a b)),
        ((nb092_alpha_dummy_010 R), (nb092_alpha_dummy_011 a b)),
        ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
        ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb092_split_alpha_0000 x y R a b)))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_a_x
                (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_a_b
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_b_y
                    (TAlphaVar.there (freshVar_injective ((R).fv) (by decide)) dv_b_x
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb092_split_alpha_0002 x y R a b dv_x_y))))
                (TAlphaClass.refl_of_reflOn
                  [((nb092_alpha_dummy_003 R), y), ((nb092_alpha_dummy_002 R), x),
                    ((nb092_alpha_dummy_001 R), b), ((nb092_alpha_dummy_000 R), a),
                    ((nb092_alpha_dummy_004 R), (nb092_alpha_dummy_005 x y R a b))] R
                  (nb092_focused_refl_0000 x y R a b dv_R_a dv_R_b dv_R_x dv_R_y)))))))))

@[expose]
noncomputable def nominal_df_lnqrel (x : Var) (y : Var) (R : Class) (a : Var) (b : Var)
    (dv_R_a : a ∉ R.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_a_b : a ≠ b) (dv_a_x : a ≠ x) (__dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_clnqrel R) (syn_copab a b
          (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
              (nb092_split_alpha_0003 x y R a b dv_R_a dv_R_b dv_R_x dv_R_y dv_a_b dv_a_x
                dv_b_x dv_b_y dv_x_y)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
