/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C074C001Part005

/-! NF weak partition development: NAR4C074C001Part006. -/


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
noncomputable def nb074_split_alpha_0001 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_035))
          (Class.cab (nb074_alpha_dummy_005)
            (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb074_alpha_dummy_035))
            (Class.cab (nb074_alpha_dummy_005)
              (syn_wrex (nb074_alpha_dummy_006) (Class.cv (nb074_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_036 x))
          (Class.cab (nb074_alpha_dummy_007 x)
            (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_036 x))
            (Class.cab (nb074_alpha_dummy_007 x)
              (syn_wrex (nb074_alpha_dummy_008 x) (Class.cv (nb074_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb074_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_006) from
                    (by
                      unfold nb074_alpha_dummy_006;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 1))))
                  (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_008 x) from (by
                      unfold nb074_alpha_dummy_008;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0036 x) 1))))
                  (TAlphaVar.there (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_005) from
                      (by
                        unfold nb074_alpha_dummy_005;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0034) 0))))
                    (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_007 x) from (by
                        unfold nb074_alpha_dummy_007;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0036 x) 0)))) (TAlphaVar.there
                      (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_035) from (by
                          unfold nb074_alpha_dummy_035;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0038) 0))))
                      (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_036 x) from (by
                          unfold nb074_alpha_dummy_036;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0039 x) 0))))
                      (TAlphaVar.there
                        (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_009) from (by
                            unfold nb074_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0035) 0))))
                        (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_010 x) from (by
                            unfold nb074_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0037 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv ∪
                      ((Class.cv (nb074_alpha_dummy_001))).fv) (by decide)) (freshVar_injective
                    (((Class.cv x)).fv ∪ ((Class.cv (nb074_alpha_dummy_002 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb074_alpha_dummy_006) ≠
        (nb074_alpha_dummy_013) from (by
          unfold nb074_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_015 x) from (by
          unfold nb074_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_014) from (by
          unfold nb074_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_016 x) from (by
          unfold nb074_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_039) from (by
          unfold nb074_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0042) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_040 x) from (by
          unfold nb074_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_037) from (by
          unfold nb074_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0040) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_038 x) from (by
          unfold nb074_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠
        (nb074_alpha_dummy_020) from (by
          unfold
            nb074_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_023 x) from (by
          unfold
            nb074_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_019)
        from (by
          unfold
            nb074_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_022 x) from (by
          unfold
            nb074_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold
            nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold
            nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017) from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb074_alpha_dummy_006) ≠
        (nb074_alpha_dummy_013) from (by
          unfold nb074_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_015 x) from (by
          unfold nb074_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_014) from (by
          unfold nb074_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_016 x) from (by
          unfold nb074_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_039) from (by
          unfold nb074_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0042) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_040 x) from (by
          unfold nb074_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0043 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_037) from (by
          unfold nb074_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0040) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_038 x) from (by
          unfold nb074_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0041 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠
        (nb074_alpha_dummy_020) from (by
          unfold
            nb074_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_023 x) from (by
          unfold
            nb074_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_019)
        from (by
          unfold
            nb074_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_022 x) from (by
          unfold
            nb074_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold
            nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold
            nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017) from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_039), (nb074_alpha_dummy_040 x)), ((nb074_alpha_dummy_037),
        (nb074_alpha_dummy_038 x)), ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
        ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_035),
        (nb074_alpha_dummy_036 x)), ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb074_alpha_dummy_037), (nb074_alpha_dummy_038 x)),
                          ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)),
                          ((nb074_alpha_dummy_005), (nb074_alpha_dummy_007 x)),
                          ((nb074_alpha_dummy_035), (nb074_alpha_dummy_036 x)),
                          ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)),
                          ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                          ((nb074_alpha_dummy_000), x),
                          ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (nb074_split_alpha_0000 x))

@[expose]
noncomputable def nb074_split_alpha_0002 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.classEq (Class.cv (nb074_alpha_dummy_003))
        (syn_cop (Class.cv (nb074_alpha_dummy_000)) (Class.cv (nb074_alpha_dummy_001))))
      (Wff.classEq (Class.cv (nb074_alpha_dummy_004 x))
        (syn_cop (Class.cv x) (Class.cv (nb074_alpha_dummy_002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
          (show (nb074_alpha_dummy_001) ≠ (nb074_alpha_dummy_003) from (by
              unfold nb074_alpha_dummy_003;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0002) 0))))) (Ne.symm
          (show (nb074_alpha_dummy_002 x) ≠ (nb074_alpha_dummy_004 x) from (by
              unfold nb074_alpha_dummy_004;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0003 x) 0)))))
        (TAlphaVar.there (Ne.symm (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_003) from
              (by
                unfold nb074_alpha_dummy_003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0000) 0))))) (Ne.symm
            (show x ≠ (nb074_alpha_dummy_004 x) from (by
                unfold nb074_alpha_dummy_004;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0001 x) 0)))))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_006) from (by
                                    unfold nb074_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0006) 1))))
                                (show x ≠ (nb074_alpha_dummy_008 x) from (by
                                    unfold nb074_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_005) from
                                    (by
                                      unfold nb074_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0006)
                                              0)))) (show x ≠ (nb074_alpha_dummy_007 x) from (by
                                      unfold nb074_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_011) from (by
                                        unfold nb074_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0010)
                                                0)))) (show x ≠ (nb074_alpha_dummy_012 x) from
                                      (by
                                        unfold nb074_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_009) from
                                        (by
                                          unfold nb074_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0007)
                                                  0)))) (show x ≠ (nb074_alpha_dummy_010 x) from
                                        (by
                                          unfold nb074_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb074_alpha_dummy_000) ≠
        (nb074_alpha_dummy_001) from (by
          unfold nb074_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0004) 0)))) (show x ≠ (nb074_alpha_dummy_002 x) from (by
          unfold nb074_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb074_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb074_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb074_alpha_dummy_006) ≠
        (nb074_alpha_dummy_013) from (by
          unfold nb074_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_015 x) from (by
          unfold nb074_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_014) from (by
          unfold nb074_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_016 x) from (by
          unfold nb074_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠
        (nb074_alpha_dummy_020) from (by
          unfold
            nb074_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_023 x) from (by
          unfold
            nb074_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_019)
        from (by
          unfold
            nb074_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_022 x) from (by
          unfold
            nb074_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold
            nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold
            nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017) from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014) 0)))) (show (nb074_alpha_dummy_015 x) ≠
        (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_006) from (by
                                    unfold nb074_alpha_dummy_006;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0006) 1))))
                                (show x ≠ (nb074_alpha_dummy_008 x) from (by
                                    unfold nb074_alpha_dummy_008;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0008 x)
                                            1)))) (TAlphaVar.there
                                  (show (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_005) from
                                    (by
                                      unfold nb074_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0006)
                                              0)))) (show x ≠ (nb074_alpha_dummy_007 x) from (by
                                      unfold nb074_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0008 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_011) from (by
                                        unfold nb074_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0010)
                                                0)))) (show x ≠ (nb074_alpha_dummy_012 x) from
                                      (by
                                        unfold nb074_alpha_dummy_012;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0011 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb074_alpha_dummy_000) ≠ (nb074_alpha_dummy_009) from
                                        (by
                                          unfold nb074_alpha_dummy_009;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0007)
                                                  0)))) (show x ≠ (nb074_alpha_dummy_010 x) from
                                        (by
                                          unfold nb074_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0009 x) 0))))
                                      (TAlphaVar.there (show (nb074_alpha_dummy_000) ≠
        (nb074_alpha_dummy_001) from (by
          unfold nb074_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0004) 0)))) (show x ≠ (nb074_alpha_dummy_002 x) from (by
          unfold nb074_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0005 x) 0)))) (TAlphaVar.here _ _ _))))))))
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective (((Class.cv (nb074_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb074_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb074_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb074_alpha_dummy_006) ≠
        (nb074_alpha_dummy_013) from (by
          unfold nb074_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 0)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_015 x) from (by
          unfold nb074_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_006) ≠ (nb074_alpha_dummy_014) from (by
          unfold nb074_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0012) 1)))) (show (nb074_alpha_dummy_008 x) ≠
        (nb074_alpha_dummy_016 x) from (by
          unfold nb074_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0013 x) 1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_008 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠
        (nb074_alpha_dummy_020) from (by
          unfold
            nb074_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  1)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_023 x) from (by
          unfold
            nb074_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  1)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_019)
        from (by
          unfold
            nb074_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0016)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_022 x) from (by
          unfold
            nb074_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0017
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold
            nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold
            nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0020)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0021
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0018)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0019
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_027) from (by
          unfold
            nb074_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0024)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_028 x) from (by
          unfold
            nb074_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0025
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_025)
        from (by
          unfold
            nb074_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0022)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_026 x) from (by
          unfold
            nb074_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0023
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_021), (nb074_alpha_dummy_024 x)), ((nb074_alpha_dummy_020),
        (nb074_alpha_dummy_023 x)), ((nb074_alpha_dummy_019), (nb074_alpha_dummy_022 x)),
        ((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_013))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠
        (nb074_alpha_dummy_031) from (by
          unfold
            nb074_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0028)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_032 x) from (by
          unfold
            nb074_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0029
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_020) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0026)
                  0)))) (show (nb074_alpha_dummy_023 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0027
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_015 x))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠
        (nb074_alpha_dummy_033) from (by
          unfold
            nb074_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0032)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_034 x) from (by
          unfold
            nb074_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0033
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_021) ≠ (nb074_alpha_dummy_029)
        from (by
          unfold
            nb074_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0030)
                  0)))) (show (nb074_alpha_dummy_024 x) ≠ (nb074_alpha_dummy_030 x) from (by
          unfold
            nb074_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0031
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017) from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014) 0)))) (show (nb074_alpha_dummy_015 x) ≠
        (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_013) ≠ (nb074_alpha_dummy_017)
        from (by
          unfold nb074_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0014)
                  0)))) (show (nb074_alpha_dummy_015 x) ≠ (nb074_alpha_dummy_018 x) from (by
          unfold nb074_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0015 x)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_017), (nb074_alpha_dummy_018 x)), ((nb074_alpha_dummy_013),
        (nb074_alpha_dummy_015 x)), ((nb074_alpha_dummy_014), (nb074_alpha_dummy_016 x)),
        ((nb074_alpha_dummy_006), (nb074_alpha_dummy_008 x)), ((nb074_alpha_dummy_005),
        (nb074_alpha_dummy_007 x)), ((nb074_alpha_dummy_011), (nb074_alpha_dummy_012 x)),
        ((nb074_alpha_dummy_009), (nb074_alpha_dummy_010 x)), ((nb074_alpha_dummy_001),
        (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
        (nb074_alpha_dummy_004 x))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb074_split_alpha_0001 x)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
