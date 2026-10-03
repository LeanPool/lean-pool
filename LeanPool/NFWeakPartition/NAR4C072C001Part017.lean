/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C072C001Part016

/-! NF weak partition development: NAR4C072C001Part017. -/


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
noncomputable def nb072_split_alpha_0007 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) R
          (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
        (syn_wbr (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) S_cls
          (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))))
      (Wff.imp (syn_wbr (Class.cv x) R (Class.cv y))
        (syn_wbr (syn_cfv H (Class.cv x)) S_cls (syn_cfv H (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_003 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072_alpha_dummy_005 x y) from (by
                                      unfold nb072_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_002 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072_alpha_dummy_004 x y) from
                                      (by
                                        unfold nb072_alpha_dummy_004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_000 A B R S_cls H) ≠
        (nb072_alpha_dummy_008 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072_alpha_dummy_009 x y) from (by
                                          unfold nb072_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_006 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072_alpha_dummy_007 x y) from (by
          unfold nb072_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072_alpha_dummy_001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_003 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072_alpha_dummy_005 x y) from (by
                                      unfold nb072_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_002 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072_alpha_dummy_004 x y) from
                                      (by
                                        unfold nb072_alpha_dummy_004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_000 A B R S_cls H) ≠
        (nb072_alpha_dummy_008 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072_alpha_dummy_009 x y) from (by
                                          unfold nb072_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_006 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072_alpha_dummy_007 x y) from (by
          unfold nb072_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072_alpha_dummy_001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0000 x y A B R S_cls H))))))))
      (TAlphaClass.refl_of_reflOn [((nb072_alpha_dummy_001 A B R S_cls H), y),
          ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        R (nb072_focused_refl_0002 x y A B R S_cls H dv_R_x dv_R_y))) (TAlphaWff.classMem
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg
                    (nb072_split_alpha_0003 x y A B R S_cls H dv_H_x dv_H_y dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072_split_alpha_0006 x y A B R S_cls H dv_H_x dv_H_y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072_split_alpha_0006 x y A B R S_cls H dv_H_x dv_H_y))))))))))))
      (TAlphaClass.refl_of_reflOn [((nb072_alpha_dummy_001 A B R S_cls H), y),
          ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        S_cls (nb072_focused_refl_0005 x y A B R S_cls H dv_S_x dv_S_y))))

@[expose]
noncomputable def nb072_split_alpha_0008 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (syn_wbr (syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H))) S_cls
          (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))))
        (syn_wbr (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)) R
          (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))))
      (Wff.imp (syn_wbr (syn_cfv H (Class.cv x)) S_cls (syn_cfv H (Class.cv y)))
        (syn_wbr (Class.cv x) R (Class.cv y))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg
                    (nb072_split_alpha_0003 x y A B R S_cls H dv_H_x dv_H_y dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072_split_alpha_0006 x y A B R S_cls H dv_H_x dv_H_y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb072_split_alpha_0006 x y A B R S_cls H dv_H_x dv_H_y))))))))))))
      (TAlphaClass.refl_of_reflOn [((nb072_alpha_dummy_001 A B R S_cls H), y),
          ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        S_cls (nb072_focused_refl_0005 x y A B R S_cls H dv_S_x dv_S_y))) (TAlphaWff.classMem
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_003 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072_alpha_dummy_005 x y) from (by
                                      unfold nb072_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_002 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072_alpha_dummy_004 x y) from
                                      (by
                                        unfold nb072_alpha_dummy_004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_000 A B R S_cls H) ≠
        (nb072_alpha_dummy_008 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072_alpha_dummy_009 x y) from (by
                                          unfold nb072_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_006 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072_alpha_dummy_007 x y) from (by
          unfold nb072_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072_alpha_dummy_001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                      (nb072_alpha_dummy_003 A B R S_cls H) from (by
                                      unfold nb072_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb072_support_mem_0000 A B R S_cls H) 1))))
                                  (show x ≠ (nb072_alpha_dummy_005 x y) from (by
                                      unfold nb072_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb072_support_mem_0002 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb072_alpha_dummy_000 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_002 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0000 A B R S_cls H)
                                                0)))) (show x ≠ (nb072_alpha_dummy_004 x y) from
                                      (by
                                        unfold nb072_alpha_dummy_004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0002 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_000 A B R S_cls H) ≠
        (nb072_alpha_dummy_008 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_008;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0004 A B R S_cls H)
                                                  0))))
                                      (show x ≠ (nb072_alpha_dummy_009 x y) from (by
                                          unfold nb072_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0005 x y) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_000 A B R S_cls H) ≠ (nb072_alpha_dummy_006 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0001 A B R S_cls H)
                  0)))) (show x ≠ (nb072_alpha_dummy_007 x y) from (by
          unfold nb072_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0003 x y) 0)))) (TAlphaVar.there (freshVar_injective
        ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) (by decide))
        dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_000 A B R S_cls H))).fv ∪ ((Class.cv
        (nb072_alpha_dummy_001 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
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
                  (nb072_support_mem_0007 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_003 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_005 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
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
        ((nb072_alpha_dummy_003 A B R S_cls H), (nb072_alpha_dummy_005 x y)),
        ((nb072_alpha_dummy_002 A B R S_cls H), (nb072_alpha_dummy_004 x y)),
        ((nb072_alpha_dummy_008 A B R S_cls H), (nb072_alpha_dummy_009 x y)),
        ((nb072_alpha_dummy_006 A B R S_cls H), (nb072_alpha_dummy_007 x y)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0000 x y A B R S_cls H))))))))
      (TAlphaClass.refl_of_reflOn [((nb072_alpha_dummy_001 A B R S_cls H), y),
          ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        R (nb072_focused_refl_0002 x y A B R S_cls H dv_R_x dv_R_y))))

@[expose]
noncomputable def nominal_df_iso (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (S_cls : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (__dv_B_x : x ∉ B.fv) (__dv_B_y : y ∉ B.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wiso H R S_cls A B) (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A
              (syn_wb (syn_wbr (.cv x) R (.cv y))
                (syn_wbr (syn_cfv H (.cv x)) S_cls (syn_cfv H (.cv y)))))))) :=
  by
  change
    Nominal.NPrf
      (Wff.biimp (syn_wiso H R S_cls A B) (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A
              (syn_wb (syn_wbr (Class.cv x) R (Class.cv y))
                (syn_wbr (syn_cfv H (Class.cv x)) S_cls (syn_cfv H (Class.cv y))))))))
  exact
    Nominal.alphaBiimp
      (TAlphaWff.conj (TAlphaWff.refl_of_reflOn [] (syn_wf1o H A B) (nb072_wpp_refl_0000 A B H))
        (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn [((nb072_alpha_dummy_000 A B R S_cls H), x)] A
                (nb072_focused_refl_0000 x A B R S_cls H dv_A_x))) (TAlphaWff.all (TAlphaWff.imp
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_reflOn [((nb072_alpha_dummy_001 A B R S_cls H), y),
                      ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                    A (nb072_focused_refl_0001 x y A B R S_cls H dv_A_x dv_A_y)))
                (TAlphaWff.conj
                  (nb072_split_alpha_0007 x y A B R S_cls H dv_H_x dv_H_y dv_R_x dv_R_y
                    dv_S_x dv_S_y dv_x_y)
                  (nb072_split_alpha_0008 x y A B R S_cls H dv_H_x dv_H_y dv_R_x dv_R_y
                    dv_S_x dv_S_y dv_x_y)))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
