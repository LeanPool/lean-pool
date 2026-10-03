/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C075C001Part004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C075C001Part005`. -/


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
noncomputable def nb075_split_alpha_0002 (x : Var) :
    TAlphaWff
      [((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x),
        ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
      (Wff.classEq (Class.cv (nb075_alpha_dummy_003))
        (syn_cop (Class.cv (nb075_alpha_dummy_000)) (Class.cv (nb075_alpha_dummy_001))))
      (Wff.classEq (Class.cv (nb075_alpha_dummy_004 x))
        (syn_cop (Class.cv x) (Class.cv (nb075_alpha_dummy_002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb075_alpha_dummy_001) ≠ (nb075_alpha_dummy_003) from (by
              unfold nb075_alpha_dummy_003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0002) 0))))) (Ne.symm
          (show (nb075_alpha_dummy_002 x) ≠ (nb075_alpha_dummy_004 x) from (by
              unfold nb075_alpha_dummy_004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0003 x) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_003) from
              (by
                unfold nb075_alpha_dummy_003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb075_alpha_dummy_004 x) from (by
                unfold nb075_alpha_dummy_004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0001 x) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_006) from (by
                                    unfold nb075_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0006) 1))))
                                (show x ≠ (nb075_alpha_dummy_008 x) from (by
                                    unfold nb075_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_005) from
                                    (by
                                      unfold nb075_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0006)
                                              0)))) (show x ≠ (nb075_alpha_dummy_007 x) from (by
                                      unfold nb075_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_011) from (by
                                        unfold nb075_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0010)
                                                0)))) (show x ≠ (nb075_alpha_dummy_012 x) from
                                      (by
                                        unfold nb075_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_009) from
                                        (by
                                          unfold nb075_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0007)
                                                  0)))) (show x ≠ (nb075_alpha_dummy_010 x) from
                                        (by
                                          unfold nb075_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb075_alpha_dummy_000) ≠
        (nb075_alpha_dummy_001) from (by
          unfold nb075_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0004) 0)))) (show x ≠ (nb075_alpha_dummy_002 x) from (by
          unfold nb075_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb075_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb075_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb075_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb075_alpha_dummy_006) ≠
        (nb075_alpha_dummy_013) from (by
          unfold nb075_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 0)))) (show (nb075_alpha_dummy_008 x) ≠
        (nb075_alpha_dummy_015 x) from (by
          unfold nb075_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb075_alpha_dummy_006) ≠ (nb075_alpha_dummy_014) from (by
          unfold nb075_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 1)))) (show (nb075_alpha_dummy_008 x) ≠
        (nb075_alpha_dummy_016 x) from (by
          unfold nb075_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠
        (nb075_alpha_dummy_020) from (by
          unfold
            nb075_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  1)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_023 x) from (by
          unfold
            nb075_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_019)
        from (by
          unfold
            nb075_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_022 x) from (by
          unfold
            nb075_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017)
        from (by
          unfold
            nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_018 x) from (by
          unfold
            nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020),
        (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)),
        ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠
        (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠
        (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020),
        (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)),
        ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠
        (nb075_alpha_dummy_031) from (by
          unfold
            nb075_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_032 x) from (by
          unfold
            nb075_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠
        (nb075_alpha_dummy_031) from (by
          unfold
            nb075_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_032 x) from (by
          unfold
            nb075_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_033) from (by
          unfold
            nb075_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_034 x) from (by
          unfold
            nb075_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠
        (nb075_alpha_dummy_033) from (by
          unfold
            nb075_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_034 x) from (by
          unfold
            nb075_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017)
        from (by
          unfold nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_018 x) from (by
          unfold nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017) from (by
          unfold nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014) 0)))) (show (nb075_alpha_dummy_015 x) ≠
        (nb075_alpha_dummy_018 x) from (by
          unfold nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017)
        from (by
          unfold nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_018 x) from (by
          unfold nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_006) from (by
                                    unfold nb075_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0006) 1))))
                                (show x ≠ (nb075_alpha_dummy_008 x) from (by
                                    unfold nb075_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_005) from
                                    (by
                                      unfold nb075_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0006)
                                              0)))) (show x ≠ (nb075_alpha_dummy_007 x) from (by
                                      unfold nb075_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_011) from (by
                                        unfold nb075_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0010)
                                                0)))) (show x ≠ (nb075_alpha_dummy_012 x) from
                                      (by
                                        unfold nb075_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_009) from
                                        (by
                                          unfold nb075_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0007)
                                                  0)))) (show x ≠ (nb075_alpha_dummy_010 x) from
                                        (by
                                          unfold nb075_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb075_alpha_dummy_000) ≠
        (nb075_alpha_dummy_001) from (by
          unfold nb075_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0004) 0)))) (show x ≠ (nb075_alpha_dummy_002 x) from (by
          unfold nb075_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb075_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb075_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb075_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb075_alpha_dummy_006) ≠
        (nb075_alpha_dummy_013) from (by
          unfold nb075_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 0)))) (show (nb075_alpha_dummy_008 x) ≠
        (nb075_alpha_dummy_015 x) from (by
          unfold nb075_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb075_alpha_dummy_006) ≠ (nb075_alpha_dummy_014) from (by
          unfold nb075_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0012) 1)))) (show (nb075_alpha_dummy_008 x) ≠
        (nb075_alpha_dummy_016 x) from (by
          unfold nb075_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠
        (nb075_alpha_dummy_020) from (by
          unfold
            nb075_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  1)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_023 x) from (by
          unfold
            nb075_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_019)
        from (by
          unfold
            nb075_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0016)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_022 x) from (by
          unfold
            nb075_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017)
        from (by
          unfold
            nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_018 x) from (by
          unfold
            nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020),
        (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)),
        ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠
        (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0020)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0018)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠
        (nb075_alpha_dummy_027) from (by
          unfold
            nb075_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0024)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_028 x) from (by
          unfold
            nb075_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_025)
        from (by
          unfold
            nb075_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0022)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_026 x) from (by
          unfold
            nb075_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_021), (nb075_alpha_dummy_024 x)), ((nb075_alpha_dummy_020),
        (nb075_alpha_dummy_023 x)), ((nb075_alpha_dummy_019), (nb075_alpha_dummy_022 x)),
        ((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_013))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠
        (nb075_alpha_dummy_031) from (by
          unfold
            nb075_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_032 x) from (by
          unfold
            nb075_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠
        (nb075_alpha_dummy_031) from (by
          unfold
            nb075_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0028)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_032 x) from (by
          unfold
            nb075_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_020) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0026)
                  0)))) (show (nb075_alpha_dummy_023 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_033) from (by
          unfold
            nb075_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_034 x) from (by
          unfold
            nb075_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠
        (nb075_alpha_dummy_033) from (by
          unfold
            nb075_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0032)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_034 x) from (by
          unfold
            nb075_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_021) ≠ (nb075_alpha_dummy_029)
        from (by
          unfold
            nb075_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0030)
                  0)))) (show (nb075_alpha_dummy_024 x) ≠ (nb075_alpha_dummy_030 x) from (by
          unfold
            nb075_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017)
        from (by
          unfold nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_018 x) from (by
          unfold nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017) from (by
          unfold nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014) 0)))) (show (nb075_alpha_dummy_015 x) ≠
        (nb075_alpha_dummy_018 x) from (by
          unfold nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_013) ≠ (nb075_alpha_dummy_017)
        from (by
          unfold nb075_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0014)
                  0)))) (show (nb075_alpha_dummy_015 x) ≠ (nb075_alpha_dummy_018 x) from (by
          unfold nb075_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_017), (nb075_alpha_dummy_018 x)), ((nb075_alpha_dummy_013),
        (nb075_alpha_dummy_015 x)), ((nb075_alpha_dummy_014), (nb075_alpha_dummy_016 x)),
        ((nb075_alpha_dummy_006), (nb075_alpha_dummy_008 x)), ((nb075_alpha_dummy_005),
        (nb075_alpha_dummy_007 x)), ((nb075_alpha_dummy_011), (nb075_alpha_dummy_012 x)),
        ((nb075_alpha_dummy_009), (nb075_alpha_dummy_010 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb075_split_alpha_0001 x)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C075C001Part006`. -/


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
noncomputable def nb075_split_alpha_0003 (x : Var) :
    TAlphaWff
      [((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)),
        ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)),
        ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)),
        ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
        ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
        ((nb075_alpha_dummy_000), x),
        ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb075_alpha_dummy_046))
          (Class.cv (nb075_alpha_dummy_041))) (Wff.neg
          (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
            (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb075_alpha_dummy_048 x))
          (Class.cv (nb075_alpha_dummy_043 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
            (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_046) from (by
              unfold nb075_alpha_dummy_046;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 1))))
          (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_048 x) from (by
              unfold nb075_alpha_dummy_048;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 1))))
          (TAlphaVar.there (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_045) from (by
                unfold nb075_alpha_dummy_045;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0072) 0))))
            (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_047 x) from (by
                unfold nb075_alpha_dummy_047;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0074 x) 0))))
            (TAlphaVar.there (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_075) from (by
                  unfold nb075_alpha_dummy_075;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0076) 0))))
              (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_076 x) from (by
                  unfold nb075_alpha_dummy_076;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0077 x) 0))))
              (TAlphaVar.there (show (nb075_alpha_dummy_041) ≠ (nb075_alpha_dummy_049) from (by
                    unfold nb075_alpha_dummy_049;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0073) 0))))
                (show (nb075_alpha_dummy_043 x) ≠ (nb075_alpha_dummy_050 x) from (by
                    unfold nb075_alpha_dummy_050;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb075_support_mem_0075 x) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb075_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((syn_cvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb075_alpha_dummy_042))).fv ∪
                ((Class.cv (nb075_alpha_dummy_041))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪
                ((Class.cv (nb075_alpha_dummy_043 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_053) from (by
                                        unfold nb075_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                0)))) (show (nb075_alpha_dummy_048 x) ≠
                                        (nb075_alpha_dummy_055 x) from (by
                                        unfold nb075_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_054) from
                                        (by
                                          unfold nb075_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0050)
                                                  1)))) (show (nb075_alpha_dummy_048 x) ≠
        (nb075_alpha_dummy_056 x) from (by
                                          unfold nb075_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb075_alpha_dummy_046) ≠
        (nb075_alpha_dummy_079) from (by
          unfold nb075_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0080) 0)))) (show (nb075_alpha_dummy_048 x) ≠
        (nb075_alpha_dummy_080 x) from (by
          unfold nb075_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_077) from (by
          unfold nb075_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0078) 0)))) (show (nb075_alpha_dummy_048 x) ≠
        (nb075_alpha_dummy_078 x) from (by
          unfold nb075_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb075_alpha_dummy_046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb075_alpha_dummy_048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_060) from (by
          unfold nb075_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_063 x) from (by
          unfold nb075_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_059)
        from (by
          unfold nb075_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_062 x) from (by
          unfold nb075_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057)
        from (by
          unfold
            nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_058 x) from (by
          unfold
            nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)), ((nb075_alpha_dummy_077),
        (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)),
        ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_075),
        (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)),
        ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041),
        (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
        ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)), ((nb075_alpha_dummy_077),
        (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)),
        ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_075),
        (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)),
        ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041),
        (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
        ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057)
        from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)),
        ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054),
        (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)),
        ((nb075_alpha_dummy_077), (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)),
        ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054),
        (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)),
        ((nb075_alpha_dummy_077), (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_053) from (by
                                        unfold nb075_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                0)))) (show (nb075_alpha_dummy_048 x) ≠
                                        (nb075_alpha_dummy_055 x) from (by
                                        unfold nb075_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_054) from
                                        (by
                                          unfold nb075_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb075_support_mem_0050)
                                                  1)))) (show (nb075_alpha_dummy_048 x) ≠
        (nb075_alpha_dummy_056 x) from (by
                                          unfold nb075_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb075_support_mem_0051 x) 1))))
                                      (TAlphaVar.there (show (nb075_alpha_dummy_046) ≠
        (nb075_alpha_dummy_079) from (by
          unfold nb075_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0080) 0)))) (show (nb075_alpha_dummy_048 x) ≠
        (nb075_alpha_dummy_080 x) from (by
          unfold nb075_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0081 x) 0)))) (TAlphaVar.there (show
        (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_077) from (by
          unfold nb075_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0078) 0)))) (show (nb075_alpha_dummy_048 x) ≠
        (nb075_alpha_dummy_078 x) from (by
          unfold nb075_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0079 x) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb075_alpha_dummy_046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb075_alpha_dummy_048 x))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_060) from (by
          unfold nb075_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_063 x) from (by
          unfold nb075_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  1)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_059)
        from (by
          unfold nb075_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_062 x) from (by
          unfold nb075_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057)
        from (by
          unfold
            nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_058 x) from (by
          unfold
            nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)), ((nb075_alpha_dummy_077),
        (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)),
        ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_075),
        (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)),
        ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041),
        (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
        ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)), ((nb075_alpha_dummy_077),
        (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)),
        ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_075),
        (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)),
        ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041),
        (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
        ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057)
        from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)),
        ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054),
        (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)),
        ((nb075_alpha_dummy_077), (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)),
        ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054),
        (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_079), (nb075_alpha_dummy_080 x)),
        ((nb075_alpha_dummy_077), (nb075_alpha_dummy_078 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb075_alpha_dummy_077), (nb075_alpha_dummy_078 x)),
                    ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)),
                    ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
                    ((nb075_alpha_dummy_075), (nb075_alpha_dummy_076 x)),
                    ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)),
                    ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
                    ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
                    ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
                    ((nb075_alpha_dummy_000), x),
                    ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C075C001Part007`. -/


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
noncomputable def nb075_split_alpha_0004 (x : Var) :
    TAlphaWff
      [((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)),
        ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
        ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
        ((nb075_alpha_dummy_000), x),
        ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb075_alpha_dummy_049)) (syn_ccompl
            (Class.cab (nb075_alpha_dummy_045)
              (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_042))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_046)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb075_alpha_dummy_049)) (syn_ccompl
              (Class.cab (nb075_alpha_dummy_045)
                (syn_wrex (nb075_alpha_dummy_046) (Class.cv (nb075_alpha_dummy_041))
                  (Wff.classEq (Class.cv (nb075_alpha_dummy_045))
                    (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_046)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb075_alpha_dummy_050 x)) (syn_ccompl
            (Class.cab (nb075_alpha_dummy_047 x)
              (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_044 x))
                (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                  (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb075_alpha_dummy_050 x)) (syn_ccompl
              (Class.cab (nb075_alpha_dummy_047 x)
                (syn_wrex (nb075_alpha_dummy_048 x) (Class.cv (nb075_alpha_dummy_043 x))
                  (Wff.classEq (Class.cv (nb075_alpha_dummy_047 x))
                    (syn_cun (syn_cphi (Class.cv (nb075_alpha_dummy_048 x)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_046) from (by
                              unfold nb075_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0044) 1))))
                          (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_048 x) from (by
                              unfold nb075_alpha_dummy_048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_045) from (by
                                unfold nb075_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0044) 0))))
                            (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_047 x) from (by
                                unfold nb075_alpha_dummy_047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_051) from (by
                                  unfold nb075_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0048) 0))))
                              (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_052 x) from
                                (by
                                  unfold nb075_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_049) from (by
                                    unfold nb075_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0045) 0)))) (show
                                  (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_050 x) from (by
                                    unfold nb075_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb075_alpha_dummy_042))).fv ∪
                              ((Class.cv (nb075_alpha_dummy_041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪
                              ((Class.cv (nb075_alpha_dummy_043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_053) from
                                    (by
                                      unfold nb075_alpha_dummy_053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0050)
                                              0)))) (show
                                    (nb075_alpha_dummy_048 x) ≠ (nb075_alpha_dummy_055 x) from
                                    (by
                                      unfold nb075_alpha_dummy_055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_054) from (by
                                        unfold nb075_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                1)))) (show (nb075_alpha_dummy_048 x) ≠
                                        (nb075_alpha_dummy_056 x) from (by
                                        unfold nb075_alpha_dummy_056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb075_alpha_dummy_046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb075_alpha_dummy_048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_060) from (by
          unfold nb075_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_063 x) from (by
          unfold nb075_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_059)
        from (by
          unfold nb075_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_062 x) from (by
          unfold nb075_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057)
        from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045),
        (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)),
        ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042),
        (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
        ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x),
        ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045),
        (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)),
        ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042),
        (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
        ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x),
        ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057),
        (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)),
        ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057),
        (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)),
        ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_046) from (by
                              unfold nb075_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0044) 1))))
                          (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_048 x) from (by
                              unfold nb075_alpha_dummy_048;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb075_support_mem_0046 x) 1))))
                          (TAlphaVar.there
                            (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_045) from (by
                                unfold nb075_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0044) 0))))
                            (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_047 x) from (by
                                unfold nb075_alpha_dummy_047;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb075_support_mem_0046 x) 0))))
                            (TAlphaVar.there
                              (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_051) from (by
                                  unfold nb075_alpha_dummy_051;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0048) 0))))
                              (show (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_052 x) from
                                (by
                                  unfold nb075_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb075_alpha_dummy_042) ≠ (nb075_alpha_dummy_049) from (by
                                    unfold nb075_alpha_dummy_049;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0045) 0)))) (show
                                  (nb075_alpha_dummy_044 x) ≠ (nb075_alpha_dummy_050 x) from (by
                                    unfold nb075_alpha_dummy_050;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0047 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb075_alpha_dummy_042))).fv ∪
                              ((Class.cv (nb075_alpha_dummy_041))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb075_alpha_dummy_044 x))).fv ∪
                              ((Class.cv (nb075_alpha_dummy_043 x))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_053) from
                                    (by
                                      unfold nb075_alpha_dummy_053;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0050)
                                              0)))) (show
                                    (nb075_alpha_dummy_048 x) ≠ (nb075_alpha_dummy_055 x) from
                                    (by
                                      unfold nb075_alpha_dummy_055;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0051 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb075_alpha_dummy_046) ≠ (nb075_alpha_dummy_054) from (by
                                        unfold nb075_alpha_dummy_054;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0050)
                                                1)))) (show (nb075_alpha_dummy_048 x) ≠
                                        (nb075_alpha_dummy_056 x) from (by
                                        unfold nb075_alpha_dummy_056;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb075_support_mem_0051 x)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb075_alpha_dummy_046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb075_alpha_dummy_048 x))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_060) from (by
          unfold nb075_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  1)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_063 x) from (by
          unfold nb075_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055 x)
                  1)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_059)
        from (by
          unfold nb075_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0054)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_062 x) from (by
          unfold nb075_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0055
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057)
        from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052)
                  0)))) (show (nb075_alpha_dummy_055 x) ≠ (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045),
        (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)),
        ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042),
        (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
        ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x),
        ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0058)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0059
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0056)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_067) from (by
          unfold
            nb075_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0062)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_068 x) from (by
          unfold
            nb075_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0063
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_065)
        from (by
          unfold
            nb075_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0060)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_066 x) from (by
          unfold
            nb075_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0061
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb075_alpha_dummy_061), (nb075_alpha_dummy_064 x)), ((nb075_alpha_dummy_060),
        (nb075_alpha_dummy_063 x)), ((nb075_alpha_dummy_059), (nb075_alpha_dummy_062 x)),
        ((nb075_alpha_dummy_057), (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053),
        (nb075_alpha_dummy_055 x)), ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)),
        ((nb075_alpha_dummy_046), (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045),
        (nb075_alpha_dummy_047 x)), ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)),
        ((nb075_alpha_dummy_049), (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042),
        (nb075_alpha_dummy_044 x)), ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
        ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x),
        ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠
        (nb075_alpha_dummy_071) from (by
          unfold
            nb075_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0066)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_072 x) from (by
          unfold
            nb075_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0067
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_060) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0064)
                  0)))) (show (nb075_alpha_dummy_063 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0065
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb075_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb075_alpha_dummy_055 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠
        (nb075_alpha_dummy_073) from (by
          unfold
            nb075_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0070)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_074 x) from (by
          unfold
            nb075_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0071
                    x)
                  0)))) (TAlphaVar.there (show (nb075_alpha_dummy_061) ≠ (nb075_alpha_dummy_069)
        from (by
          unfold
            nb075_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0068)
                  0)))) (show (nb075_alpha_dummy_064 x) ≠ (nb075_alpha_dummy_070 x) from (by
          unfold
            nb075_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0069
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057),
        (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)),
        ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb075_alpha_dummy_053) ≠ (nb075_alpha_dummy_057) from (by
          unfold nb075_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0052) 0)))) (show (nb075_alpha_dummy_055 x) ≠
        (nb075_alpha_dummy_058 x) from (by
          unfold nb075_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb075_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb075_alpha_dummy_057),
        (nb075_alpha_dummy_058 x)), ((nb075_alpha_dummy_053), (nb075_alpha_dummy_055 x)),
        ((nb075_alpha_dummy_054), (nb075_alpha_dummy_056 x)), ((nb075_alpha_dummy_046),
        (nb075_alpha_dummy_048 x)), ((nb075_alpha_dummy_045), (nb075_alpha_dummy_047 x)),
        ((nb075_alpha_dummy_051), (nb075_alpha_dummy_052 x)), ((nb075_alpha_dummy_049),
        (nb075_alpha_dummy_050 x)), ((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
        ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)), ((nb075_alpha_dummy_001),
        (nb075_alpha_dummy_002 x)), ((nb075_alpha_dummy_000), x), ((nb075_alpha_dummy_003),
        (nb075_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb075_split_alpha_0003 x)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb075_split_alpha_0003 x)))))))))))

@[expose]
noncomputable def nominal_df_ranfn (x : Var) :
    Nominal.NPrf (.classEq (syn_cranfn) (syn_cmpt x (syn_cvv) (syn_crn (.cv x)))) := by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb075_split_alpha_0002 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_001) from (by
                          unfold nb075_alpha_dummy_001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0004) 0))))
                      (show x ≠ (nb075_alpha_dummy_002 x) from (by
                          unfold nb075_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb075_support_mem_0005 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
                      ((nb075_alpha_dummy_000), x),
                      ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
                    (syn_cvv) (by simp only [fv_syn_cvv])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb075_alpha_dummy_042), (nb075_alpha_dummy_044 x)),
                              ((nb075_alpha_dummy_041), (nb075_alpha_dummy_043 x)),
                              ((nb075_alpha_dummy_001), (nb075_alpha_dummy_002 x)),
                              ((nb075_alpha_dummy_000), x),
                              ((nb075_alpha_dummy_003), (nb075_alpha_dummy_004 x))]
                            (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                          (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.neg (nb075_split_alpha_0004 x))))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_042) from (by
                                  unfold nb075_alpha_dummy_042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0082) 1))))
                              (show x ≠ (nb075_alpha_dummy_044 x) from (by
                                  unfold nb075_alpha_dummy_044;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb075_support_mem_0083 x) 1))))
                              (TAlphaVar.there
                                (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_041) from (by
                                    unfold nb075_alpha_dummy_041;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0082) 0))))
                                (show x ≠ (nb075_alpha_dummy_043 x) from (by
                                    unfold nb075_alpha_dummy_043;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb075_support_mem_0083 x)
                                            0)))) (TAlphaVar.there
                                  (show (nb075_alpha_dummy_000) ≠ (nb075_alpha_dummy_001) from
                                    (by
                                      unfold nb075_alpha_dummy_001;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0004)
                                              0)))) (show x ≠ (nb075_alpha_dummy_002 x) from (by
                                      unfold nb075_alpha_dummy_002;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb075_support_mem_0005 x)
                                              0)))) (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
