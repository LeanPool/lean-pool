/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C073C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C073C001Part004`. -/


section

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
noncomputable def nb073_split_alpha_0000 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
        ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
        ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
        ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
        ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
        ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
        ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_020))
          (Class.cab (nb073_alpha_dummy_014)
            (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                (syn_cphi (Class.cv (nb073_alpha_dummy_015))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_020)) (Class.cab (nb073_alpha_dummy_014)
              (syn_wrex (nb073_alpha_dummy_015) (Class.cv (nb073_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb073_alpha_dummy_014))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_015)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_021 x y))
          (Class.cab (nb073_alpha_dummy_016 x y)
            (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_021 x y))
            (Class.cab (nb073_alpha_dummy_016 x y)
              (syn_wrex (nb073_alpha_dummy_017 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb073_alpha_dummy_016 x y))
                  (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_015) from
                    (by
                      unfold nb073_alpha_dummy_015;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
                  (show x ≠ (nb073_alpha_dummy_017 x y) from (by
                      unfold nb073_alpha_dummy_017;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb073_support_mem_0016 x y) 1)))) (TAlphaVar.there
                    (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_014) from (by
                        unfold nb073_alpha_dummy_014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 0))))
                    (show x ≠ (nb073_alpha_dummy_016 x y) from (by
                        unfold nb073_alpha_dummy_016;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
                    (TAlphaVar.there
                      (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_020) from (by
                          unfold nb073_alpha_dummy_020;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0018) 0))))
                      (show x ≠ (nb073_alpha_dummy_021 x y) from (by
                          unfold nb073_alpha_dummy_021;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0019 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_018) from (by
                            unfold nb073_alpha_dummy_018;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0015) 0))))
                        (show x ≠ (nb073_alpha_dummy_019 x y) from (by
                            unfold nb073_alpha_dummy_019;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0017 x y) 0))))
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_007) from (by
                              unfold nb073_alpha_dummy_007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0008) 1))))
                          (show x ≠ (nb073_alpha_dummy_009 x y) from (by
                              unfold nb073_alpha_dummy_009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_006) from (by
                                unfold nb073_alpha_dummy_006;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0008) 0))))
                            (show x ≠ (nb073_alpha_dummy_008 x y) from (by
                                unfold nb073_alpha_dummy_008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0010 x y) 0))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_012) from (by
                                  unfold nb073_alpha_dummy_012;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0012) 0))))
                              (show x ≠ (nb073_alpha_dummy_013 x y) from (by
                                  unfold nb073_alpha_dummy_013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0013 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_010) from (by
                                    unfold nb073_alpha_dummy_010;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0009) 0))))
                                (show x ≠ (nb073_alpha_dummy_011 x y) from (by
                                    unfold nb073_alpha_dummy_011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0011 x y)
                                            0)))) (TAlphaVar.there
                                  (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_002) from
                                    (by
                                      unfold nb073_alpha_dummy_002;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0006)
                                              0)))) (show x ≠ (nb073_alpha_dummy_003 x y) from
                                    (by
                                      unfold nb073_alpha_dummy_003;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0007 x y)
                                              0)))) (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_x_y (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb073_alpha_dummy_000))).fv ∪
                      ((Class.cv (nb073_alpha_dummy_001))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_022) from (by
                              unfold nb073_alpha_dummy_022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0020) 0))))
                          (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_024 x y) from
                            (by
                              unfold nb073_alpha_dummy_024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_023) from (by
                                unfold nb073_alpha_dummy_023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                              (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_025 x y) from (by
                                unfold nb073_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073_alpha_dummy_015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_029) from (by
          unfold nb073_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_032 x y) from (by
          unfold nb073_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_028) from (by
          unfold nb073_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_031 x y) from (by
          unfold nb073_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026)
        from (by
          unfold nb073_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022) 0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_027 x y) from (by
          unfold nb073_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
        ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007),
        (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
        ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010),
        (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
        (nb073_alpha_dummy_005 x y))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
        ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007),
        (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
        ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010),
        (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
        (nb073_alpha_dummy_005 x y))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_040) from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_040)
        from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠
        (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from (by
                                        unfold nb073_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                        (nb073_alpha_dummy_027 x y) from (by
                                        unfold nb073_alpha_dummy_027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                    ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                    ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
                                    ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                    ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                    ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                    ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                    ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from
                                    (by
                                      unfold nb073_alpha_dummy_026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0022)
                                              0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                      (nb073_alpha_dummy_027 x y) from (by
                                      unfold nb073_alpha_dummy_027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from (by
                                        unfold nb073_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                        (nb073_alpha_dummy_027 x y) from (by
                                        unfold nb073_alpha_dummy_027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                    ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                    ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
                                    ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                    ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                    ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                    ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                    ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_015) from
                      (by
                        unfold nb073_alpha_dummy_015;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb073_support_mem_0014) 1))))
                    (show x ≠ (nb073_alpha_dummy_017 x y) from (by
                        unfold nb073_alpha_dummy_017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb073_support_mem_0016 x y) 1))))
                    (TAlphaVar.there
                      (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_014) from (by
                          unfold nb073_alpha_dummy_014;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0014) 0))))
                      (show x ≠ (nb073_alpha_dummy_016 x y) from (by
                          unfold nb073_alpha_dummy_016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb073_support_mem_0016 x y) 0))))
                      (TAlphaVar.there
                        (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_020) from (by
                            unfold nb073_alpha_dummy_020;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0018) 0))))
                        (show x ≠ (nb073_alpha_dummy_021 x y) from (by
                            unfold nb073_alpha_dummy_021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb073_support_mem_0019 x y) 0))))
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_018) from (by
                              unfold nb073_alpha_dummy_018;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0015) 0))))
                          (show x ≠ (nb073_alpha_dummy_019 x y) from (by
                              unfold nb073_alpha_dummy_019;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0017 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_007) from (by
                                unfold nb073_alpha_dummy_007;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0008) 1))))
                            (show x ≠ (nb073_alpha_dummy_009 x y) from (by
                                unfold nb073_alpha_dummy_009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0010 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_006) from (by
                                  unfold nb073_alpha_dummy_006;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0008) 0))))
                              (show x ≠ (nb073_alpha_dummy_008 x y) from (by
                                  unfold nb073_alpha_dummy_008;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0010 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_012) from (by
                                    unfold nb073_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0012) 0))))
                                (show x ≠ (nb073_alpha_dummy_013 x y) from (by
                                    unfold nb073_alpha_dummy_013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0013 x y)
                                            0)))) (TAlphaVar.there
                                  (show (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_010) from
                                    (by
                                      unfold nb073_alpha_dummy_010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0009)
                                              0)))) (show x ≠ (nb073_alpha_dummy_011 x y) from
                                    (by
                                      unfold nb073_alpha_dummy_011;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0011 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb073_alpha_dummy_000) ≠ (nb073_alpha_dummy_002) from (by
                                        unfold nb073_alpha_dummy_002;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0006)
                                                0)))) (show x ≠ (nb073_alpha_dummy_003 x y) from
                                      (by
                                        unfold nb073_alpha_dummy_003;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0007 x y) 0))))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      dv_x_y (TAlphaVar.here _ _ _)))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb073_alpha_dummy_000))).fv ∪
                        ((Class.cv (nb073_alpha_dummy_001))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_022) from (by
                                unfold nb073_alpha_dummy_022;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 0)))) (show
                              (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_024 x y) from (by
                                unfold nb073_alpha_dummy_024;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_023) from (by
                                  unfold nb073_alpha_dummy_023;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                                (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_025 x y) from
                                (by
                                  unfold nb073_alpha_dummy_025;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0021 x y)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb073_alpha_dummy_015))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_029) from (by
          unfold nb073_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_032 x y) from (by
          unfold nb073_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  1)))) (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_028)
        from (by
          unfold nb073_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_031 x y) from (by
          unfold nb073_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026)
        from (by
          unfold nb073_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022)
                  0)))) (show (nb073_alpha_dummy_024 x y) ≠ (nb073_alpha_dummy_027 x y) from (by
          unfold nb073_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
        ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007),
        (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
        ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010),
        (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
        (nb073_alpha_dummy_005 x y))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)), ((nb073_alpha_dummy_014),
        (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
        ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)), ((nb073_alpha_dummy_007),
        (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
        ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)), ((nb073_alpha_dummy_010),
        (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
        (nb073_alpha_dummy_005 x y))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_040) from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_040)
        from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠
        (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from
                                        (by
                                          unfold nb073_alpha_dummy_026;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0022)
                                                  0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_027 x y) from (by
                                          unfold nb073_alpha_dummy_027;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0023 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                      ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                      ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                      ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                      ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                      ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
                                      ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                      ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                      ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                      ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                      ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                      ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                      ((nb073_alpha_dummy_001), y),
                                      ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
                                        (nb073_alpha_dummy_005 x y))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from (by
                                        unfold nb073_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                        (nb073_alpha_dummy_027 x y) from (by
                                        unfold nb073_alpha_dummy_027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from
                                        (by
                                          unfold nb073_alpha_dummy_026;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb073_support_mem_0022)
                                                  0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_027 x y) from (by
                                          unfold nb073_alpha_dummy_027;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb073_support_mem_0023 x y) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                      ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                      ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                      ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                      ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                      ((nb073_alpha_dummy_020), (nb073_alpha_dummy_021 x y)),
                                      ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                      ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                      ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                      ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                      ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                      ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                      ((nb073_alpha_dummy_001), y),
                                      ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004),
                                        (nb073_alpha_dummy_005 x y))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C073C001Part005`. -/


section

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
noncomputable def nb073_split_alpha_0001 (x : Var) (y : Var) :
    TAlphaWff
      [((nb073_alpha_dummy_046), (nb073_alpha_dummy_047 x y)),
        ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
        ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
        ((nb073_alpha_dummy_044), (nb073_alpha_dummy_045 x y)),
        ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
        ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
        ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
        ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
        ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
        ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
        ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
        ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_046))
          (syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_015))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_046)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb073_alpha_dummy_047 x y))
          (syn_ccompl (syn_cphi (Class.cv (nb073_alpha_dummy_017 x y))))) (Wff.neg
          (Wff.classMem (Class.cv (nb073_alpha_dummy_047 x y))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_022) from (by
                              unfold nb073_alpha_dummy_022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0020) 0))))
                          (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_024 x y) from
                            (by
                              unfold nb073_alpha_dummy_024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_023) from (by
                                unfold nb073_alpha_dummy_023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                              (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_025 x y) from (by
                                unfold nb073_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_048) from (by
                                  unfold nb073_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0058) 0)))) (show
                                (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_049 x y) from
                                (by
                                  unfold nb073_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0059 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_046) from (by
                                    unfold nb073_alpha_dummy_046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0056) 0)))) (show
                                  (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_047 x y) from
                                  (by
                                    unfold nb073_alpha_dummy_047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0057 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073_alpha_dummy_015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_029) from (by
          unfold nb073_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_032 x y) from (by
          unfold nb073_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_028) from (by
          unfold nb073_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_031 x y) from (by
          unfold nb073_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026)
        from (by
          unfold nb073_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022) 0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_027 x y) from (by
          unfold nb073_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)), ((nb073_alpha_dummy_046),
        (nb073_alpha_dummy_047 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
        ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_044),
        (nb073_alpha_dummy_045 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
        ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006),
        (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
        ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)), ((nb073_alpha_dummy_046),
        (nb073_alpha_dummy_047 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
        ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_044),
        (nb073_alpha_dummy_045 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
        ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006),
        (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
        ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠
        (nb073_alpha_dummy_040) from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_040)
        from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠
        (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from (by
                                        unfold nb073_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                        (nb073_alpha_dummy_027 x y) from (by
                                        unfold nb073_alpha_dummy_027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                    ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                    ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                    ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)),
                                    ((nb073_alpha_dummy_046), (nb073_alpha_dummy_047 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_044), (nb073_alpha_dummy_045 x y)),
                                    ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                    ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                    ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                    ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                    ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from
                                    (by
                                      unfold nb073_alpha_dummy_026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0022)
                                              0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                      (nb073_alpha_dummy_027 x y) from (by
                                      unfold nb073_alpha_dummy_027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from (by
                                        unfold nb073_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                        (nb073_alpha_dummy_027 x y) from (by
                                        unfold nb073_alpha_dummy_027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                    ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                    ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                    ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)),
                                    ((nb073_alpha_dummy_046), (nb073_alpha_dummy_047 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_044), (nb073_alpha_dummy_045 x y)),
                                    ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                    ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                    ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                    ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                    ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_022) from (by
                              unfold nb073_alpha_dummy_022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0020) 0))))
                          (show (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_024 x y) from
                            (by
                              unfold nb073_alpha_dummy_024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb073_support_mem_0021 x y) 0))))
                          (TAlphaVar.there
                            (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_023) from (by
                                unfold nb073_alpha_dummy_023;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0020) 1)))) (show
                              (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_025 x y) from (by
                                unfold nb073_alpha_dummy_025;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb073_support_mem_0021 x y) 1))))
                            (TAlphaVar.there
                              (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_048) from (by
                                  unfold nb073_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0058) 0)))) (show
                                (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_049 x y) from
                                (by
                                  unfold nb073_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb073_support_mem_0059 x y)
                                          0)))) (TAlphaVar.there
                                (show (nb073_alpha_dummy_015) ≠ (nb073_alpha_dummy_046) from (by
                                    unfold nb073_alpha_dummy_046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0056) 0)))) (show
                                  (nb073_alpha_dummy_017 x y) ≠ (nb073_alpha_dummy_047 x y) from
                                  (by
                                    unfold nb073_alpha_dummy_047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb073_support_mem_0057 x y)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb073_alpha_dummy_015))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb073_alpha_dummy_017 x y))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_029) from (by
          unfold nb073_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 1)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_032 x y) from (by
          unfold nb073_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y) 1)))) (TAlphaVar.there (show
        (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_028) from (by
          unfold nb073_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0024) 0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_031 x y) from (by
          unfold nb073_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0025 x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026)
        from (by
          unfold nb073_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0022) 0)))) (show (nb073_alpha_dummy_024 x y) ≠
        (nb073_alpha_dummy_027 x y) from (by
          unfold nb073_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0023 x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)), ((nb073_alpha_dummy_046),
        (nb073_alpha_dummy_047 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
        ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_044),
        (nb073_alpha_dummy_045 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
        ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006),
        (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
        ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_036) from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0028)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0029
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0026)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0027
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_036)
        from (by
          unfold
            nb073_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0032)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_037 x y) from (by
          unfold
            nb073_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0033
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_034)
        from (by
          unfold
            nb073_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0030)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_035 x y) from (by
          unfold
            nb073_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0031
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb073_alpha_dummy_030), (nb073_alpha_dummy_033 x y)), ((nb073_alpha_dummy_029),
        (nb073_alpha_dummy_032 x y)), ((nb073_alpha_dummy_028), (nb073_alpha_dummy_031 x y)),
        ((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)), ((nb073_alpha_dummy_022),
        (nb073_alpha_dummy_024 x y)), ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
        ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)), ((nb073_alpha_dummy_046),
        (nb073_alpha_dummy_047 x y)), ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
        ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)), ((nb073_alpha_dummy_044),
        (nb073_alpha_dummy_045 x y)), ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
        ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)), ((nb073_alpha_dummy_006),
        (nb073_alpha_dummy_008 x y)), ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
        ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)), ((nb073_alpha_dummy_002),
        (nb073_alpha_dummy_003 x y)), ((nb073_alpha_dummy_001), y),
        ((nb073_alpha_dummy_000), x), ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb073_alpha_dummy_022))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb073_alpha_dummy_024 x
        y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠
        (nb073_alpha_dummy_040) from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_040)
        from (by
          unfold
            nb073_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0036)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_041 x y) from (by
          unfold
            nb073_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_029) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0034)
                  0)))) (show (nb073_alpha_dummy_032 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0035
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb073_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb073_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠
        (nb073_alpha_dummy_042) from (by
          unfold
            nb073_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0040)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_043 x y) from (by
          unfold
            nb073_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0041
                    x y)
                  0)))) (TAlphaVar.there (show (nb073_alpha_dummy_030) ≠ (nb073_alpha_dummy_038)
        from (by
          unfold
            nb073_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0038)
                  0)))) (show (nb073_alpha_dummy_033 x y) ≠ (nb073_alpha_dummy_039 x y) from (by
          unfold
            nb073_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb073_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from (by
                                        unfold nb073_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                        (nb073_alpha_dummy_027 x y) from (by
                                        unfold nb073_alpha_dummy_027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                    ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                    ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                    ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)),
                                    ((nb073_alpha_dummy_046), (nb073_alpha_dummy_047 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_044), (nb073_alpha_dummy_045 x y)),
                                    ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                    ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                    ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                    ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                    ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from
                                    (by
                                      unfold nb073_alpha_dummy_026;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0022)
                                              0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                      (nb073_alpha_dummy_027 x y) from (by
                                      unfold nb073_alpha_dummy_027;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb073_support_mem_0023 x y)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb073_alpha_dummy_022) ≠ (nb073_alpha_dummy_026) from (by
                                        unfold nb073_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb073_support_mem_0022)
                                                0)))) (show (nb073_alpha_dummy_024 x y) ≠
                                        (nb073_alpha_dummy_027 x y) from (by
                                        unfold nb073_alpha_dummy_027;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb073_support_mem_0023 x y) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb073_alpha_dummy_026), (nb073_alpha_dummy_027 x y)),
                                    ((nb073_alpha_dummy_022), (nb073_alpha_dummy_024 x y)),
                                    ((nb073_alpha_dummy_023), (nb073_alpha_dummy_025 x y)),
                                    ((nb073_alpha_dummy_048), (nb073_alpha_dummy_049 x y)),
                                    ((nb073_alpha_dummy_046), (nb073_alpha_dummy_047 x y)),
                                    ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
                                    ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
                                    ((nb073_alpha_dummy_044), (nb073_alpha_dummy_045 x y)),
                                    ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
                                    ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
                                    ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
                                    ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
                                    ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
                                    ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
                                    ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
                                    ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb073_alpha_dummy_046), (nb073_alpha_dummy_047 x y)),
            ((nb073_alpha_dummy_015), (nb073_alpha_dummy_017 x y)),
            ((nb073_alpha_dummy_014), (nb073_alpha_dummy_016 x y)),
            ((nb073_alpha_dummy_044), (nb073_alpha_dummy_045 x y)),
            ((nb073_alpha_dummy_018), (nb073_alpha_dummy_019 x y)),
            ((nb073_alpha_dummy_007), (nb073_alpha_dummy_009 x y)),
            ((nb073_alpha_dummy_006), (nb073_alpha_dummy_008 x y)),
            ((nb073_alpha_dummy_012), (nb073_alpha_dummy_013 x y)),
            ((nb073_alpha_dummy_010), (nb073_alpha_dummy_011 x y)),
            ((nb073_alpha_dummy_002), (nb073_alpha_dummy_003 x y)),
            ((nb073_alpha_dummy_001), y), ((nb073_alpha_dummy_000), x),
            ((nb073_alpha_dummy_004), (nb073_alpha_dummy_005 x y))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
