/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C094M3Part002

/-! NF weak partition development: NAR4H5C094M3Part003. -/


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
noncomputable def nb094_split_alpha_0003 (x : Var) (y : Var) :
    TAlphaWff
      [((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)),
        ((nb094_alpha_dummy_072), (nb094_alpha_dummy_073 x y)),
        ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)),
        ((nb094_alpha_dummy_001), y), ((nb094_alpha_dummy_000), x),
        ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb094_alpha_dummy_007))
          (Class.cv (nb094_alpha_dummy_002))) (Wff.neg
          (Wff.classEq (Class.cv (nb094_alpha_dummy_006))
            (syn_cun (syn_cphi (Class.cv (nb094_alpha_dummy_007))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb094_alpha_dummy_009 x y))
          (Class.cv (nb094_alpha_dummy_003 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb094_alpha_dummy_008 x y))
            (syn_cun (syn_cphi (Class.cv (nb094_alpha_dummy_009 x y)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_002) ≠ (nb094_alpha_dummy_007) from (by
              unfold nb094_alpha_dummy_007;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 1))))
          (show (nb094_alpha_dummy_003 x y) ≠ (nb094_alpha_dummy_009 x y) from (by
              unfold nb094_alpha_dummy_009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 1))))
          (TAlphaVar.there (show (nb094_alpha_dummy_002) ≠ (nb094_alpha_dummy_006) from (by
                unfold nb094_alpha_dummy_006;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 0))))
            (show (nb094_alpha_dummy_003 x y) ≠ (nb094_alpha_dummy_008 x y) from (by
                unfold nb094_alpha_dummy_008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 0))))
            (TAlphaVar.there (show (nb094_alpha_dummy_002) ≠ (nb094_alpha_dummy_072) from (by
                  unfold nb094_alpha_dummy_072;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0086) 0))))
              (show (nb094_alpha_dummy_003 x y) ≠ (nb094_alpha_dummy_073 x y) from (by
                  unfold nb094_alpha_dummy_073;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0087 x y) 0))))
              (TAlphaVar.there (show (nb094_alpha_dummy_002) ≠ (nb094_alpha_dummy_010) from (by
                    unfold nb094_alpha_dummy_010;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0083) 0))))
                (show (nb094_alpha_dummy_003 x y) ≠ (nb094_alpha_dummy_011 x y) from (by
                    unfold nb094_alpha_dummy_011;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0085 x y) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb094_alpha_dummy_000))
                    (Class.cv (nb094_alpha_dummy_001)))).fv ∪
                ((Class.cv (nb094_alpha_dummy_002))).fv) (by decide)) (freshVar_injective
              (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb094_alpha_dummy_003 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094_alpha_dummy_007) ≠ (nb094_alpha_dummy_050) from (by
                                        unfold nb094_alpha_dummy_050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0060)
                                                0)))) (show (nb094_alpha_dummy_009 x y) ≠
                                        (nb094_alpha_dummy_052 x y) from (by
                                        unfold nb094_alpha_dummy_052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0061 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb094_alpha_dummy_007) ≠ (nb094_alpha_dummy_051) from
                                        (by
                                          unfold nb094_alpha_dummy_051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0060)
                                                  1)))) (show (nb094_alpha_dummy_009 x y) ≠
        (nb094_alpha_dummy_053 x y) from (by
                                          unfold nb094_alpha_dummy_053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0061 x y) 1))))
                                      (TAlphaVar.there (show (nb094_alpha_dummy_007) ≠
        (nb094_alpha_dummy_076) from (by
          unfold nb094_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0090) 0)))) (show (nb094_alpha_dummy_009 x y) ≠
        (nb094_alpha_dummy_077 x y) from (by
          unfold nb094_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0091 x y) 0)))) (TAlphaVar.there (show
        (nb094_alpha_dummy_007) ≠ (nb094_alpha_dummy_074) from (by
          unfold nb094_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0088) 0)))) (show (nb094_alpha_dummy_009 x y) ≠
        (nb094_alpha_dummy_075 x y) from (by
          unfold nb094_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0089 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb094_alpha_dummy_007))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb094_alpha_dummy_009 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_057) from (by
          unfold nb094_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  1)))) (show (nb094_alpha_dummy_052 x y) ≠ (nb094_alpha_dummy_060 x y) from (by
          unfold nb094_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  1)))) (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_056)
        from (by
          unfold nb094_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  0)))) (show (nb094_alpha_dummy_052 x y) ≠ (nb094_alpha_dummy_059 x y) from (by
          unfold nb094_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054)
        from (by
          unfold
            nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062)
                  0)))) (show (nb094_alpha_dummy_052 x y) ≠ (nb094_alpha_dummy_055 x y) from (by
          unfold
            nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_058), (nb094_alpha_dummy_061 x y)), ((nb094_alpha_dummy_057),
        (nb094_alpha_dummy_060 x y)), ((nb094_alpha_dummy_056), (nb094_alpha_dummy_059 x y)),
        ((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠
        (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠
        (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_058), (nb094_alpha_dummy_061 x y)), ((nb094_alpha_dummy_057),
        (nb094_alpha_dummy_060 x y)), ((nb094_alpha_dummy_056), (nb094_alpha_dummy_059 x y)),
        ((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094_alpha_dummy_050))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052
        x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠
        (nb094_alpha_dummy_068) from (by
          unfold
            nb094_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_069 x y) from (by
          unfold
            nb094_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠
        (nb094_alpha_dummy_068) from (by
          unfold
            nb094_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_069 x y) from (by
          unfold
            nb094_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_070) from (by
          unfold
            nb094_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_071 x y) from (by
          unfold
            nb094_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠
        (nb094_alpha_dummy_070) from (by
          unfold
            nb094_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_071 x y) from (by
          unfold
            nb094_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054)
        from (by
          unfold nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094_alpha_dummy_052 x y) ≠
        (nb094_alpha_dummy_055 x y) from (by
          unfold nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054) from (by
          unfold nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094_alpha_dummy_052 x y) ≠
        (nb094_alpha_dummy_055 x y) from (by
          unfold nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054) from (by
          unfold nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094_alpha_dummy_052 x y) ≠
        (nb094_alpha_dummy_055 x y) from (by
          unfold nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094_alpha_dummy_007) ≠ (nb094_alpha_dummy_050) from (by
                                        unfold nb094_alpha_dummy_050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0060)
                                                0)))) (show (nb094_alpha_dummy_009 x y) ≠
                                        (nb094_alpha_dummy_052 x y) from (by
                                        unfold nb094_alpha_dummy_052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0061 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb094_alpha_dummy_007) ≠ (nb094_alpha_dummy_051) from
                                        (by
                                          unfold nb094_alpha_dummy_051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0060)
                                                  1)))) (show (nb094_alpha_dummy_009 x y) ≠
        (nb094_alpha_dummy_053 x y) from (by
                                          unfold nb094_alpha_dummy_053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0061 x y) 1))))
                                      (TAlphaVar.there (show (nb094_alpha_dummy_007) ≠
        (nb094_alpha_dummy_076) from (by
          unfold nb094_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0090) 0)))) (show (nb094_alpha_dummy_009 x y) ≠
        (nb094_alpha_dummy_077 x y) from (by
          unfold nb094_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0091 x y) 0)))) (TAlphaVar.there (show
        (nb094_alpha_dummy_007) ≠ (nb094_alpha_dummy_074) from (by
          unfold nb094_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0088) 0)))) (show (nb094_alpha_dummy_009 x y) ≠
        (nb094_alpha_dummy_075 x y) from (by
          unfold nb094_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0089 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb094_alpha_dummy_007))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb094_alpha_dummy_009 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_057) from (by
          unfold nb094_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  1)))) (show (nb094_alpha_dummy_052 x y) ≠ (nb094_alpha_dummy_060 x y) from (by
          unfold nb094_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  1)))) (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_056)
        from (by
          unfold nb094_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  0)))) (show (nb094_alpha_dummy_052 x y) ≠ (nb094_alpha_dummy_059 x y) from (by
          unfold nb094_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054)
        from (by
          unfold
            nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062)
                  0)))) (show (nb094_alpha_dummy_052 x y) ≠ (nb094_alpha_dummy_055 x y) from (by
          unfold
            nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_058), (nb094_alpha_dummy_061 x y)), ((nb094_alpha_dummy_057),
        (nb094_alpha_dummy_060 x y)), ((nb094_alpha_dummy_056), (nb094_alpha_dummy_059 x y)),
        ((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠
        (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠
        (nb094_alpha_dummy_064) from (by
          unfold
            nb094_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_065 x y) from (by
          unfold
            nb094_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_062)
        from (by
          unfold
            nb094_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_063 x y) from (by
          unfold
            nb094_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_058), (nb094_alpha_dummy_061 x y)), ((nb094_alpha_dummy_057),
        (nb094_alpha_dummy_060 x y)), ((nb094_alpha_dummy_056), (nb094_alpha_dummy_059 x y)),
        ((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094_alpha_dummy_050))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052
        x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠
        (nb094_alpha_dummy_068) from (by
          unfold
            nb094_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_069 x y) from (by
          unfold
            nb094_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠
        (nb094_alpha_dummy_068) from (by
          unfold
            nb094_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_069 x y) from (by
          unfold
            nb094_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_057) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094_alpha_dummy_060 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094_alpha_dummy_052 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_070) from (by
          unfold
            nb094_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_071 x y) from (by
          unfold
            nb094_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠
        (nb094_alpha_dummy_070) from (by
          unfold
            nb094_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_071 x y) from (by
          unfold
            nb094_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_058) ≠ (nb094_alpha_dummy_066)
        from (by
          unfold
            nb094_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094_alpha_dummy_061 x y) ≠ (nb094_alpha_dummy_067 x y) from (by
          unfold
            nb094_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054)
        from (by
          unfold nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094_alpha_dummy_052 x y) ≠
        (nb094_alpha_dummy_055 x y) from (by
          unfold nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054) from (by
          unfold nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094_alpha_dummy_052 x y) ≠
        (nb094_alpha_dummy_055 x y) from (by
          unfold nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb094_alpha_dummy_050) ≠ (nb094_alpha_dummy_054) from (by
          unfold nb094_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094_alpha_dummy_052 x y) ≠
        (nb094_alpha_dummy_055 x y) from (by
          unfold nb094_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb094_alpha_dummy_054), (nb094_alpha_dummy_055 x y)), ((nb094_alpha_dummy_050),
        (nb094_alpha_dummy_052 x y)), ((nb094_alpha_dummy_051), (nb094_alpha_dummy_053 x y)),
        ((nb094_alpha_dummy_076), (nb094_alpha_dummy_077 x y)), ((nb094_alpha_dummy_074),
        (nb094_alpha_dummy_075 x y)), ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
        ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)), ((nb094_alpha_dummy_072),
        (nb094_alpha_dummy_073 x y)), ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
        ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)), ((nb094_alpha_dummy_001), y),
        ((nb094_alpha_dummy_000), x), ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb094_alpha_dummy_074), (nb094_alpha_dummy_075 x y)),
                    ((nb094_alpha_dummy_007), (nb094_alpha_dummy_009 x y)),
                    ((nb094_alpha_dummy_006), (nb094_alpha_dummy_008 x y)),
                    ((nb094_alpha_dummy_072), (nb094_alpha_dummy_073 x y)),
                    ((nb094_alpha_dummy_010), (nb094_alpha_dummy_011 x y)),
                    ((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)),
                    ((nb094_alpha_dummy_001), y), ((nb094_alpha_dummy_000), x),
                    ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nominal_df_lndifop (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_clndifop)
        (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cdif (.cv x) (.cv y)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb094_alpha_dummy_002) ≠ (nb094_alpha_dummy_004) from (by
                            unfold nb094_alpha_dummy_004;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0004) 0))))) (Ne.symm
                        (show (nb094_alpha_dummy_003 x y) ≠ (nb094_alpha_dummy_005 x y) from (by
                            unfold nb094_alpha_dummy_005;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0005 x y) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_004) from (by
                              unfold nb094_alpha_dummy_004;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0002) 0))))) (Ne.symm
                          (show y ≠ (nb094_alpha_dummy_005 x y) from (by
                              unfold nb094_alpha_dummy_005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0003 x y) 0)))))
                        (TAlphaVar.there (Ne.symm
                            (show (nb094_alpha_dummy_000) ≠ (nb094_alpha_dummy_004) from (by
                                unfold nb094_alpha_dummy_004;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0000) 0))))) (Ne.symm
                            (show x ≠ (nb094_alpha_dummy_005 x y) from (by
                                unfold nb094_alpha_dummy_005;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0001 x y) 0)))))
                          (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb094_split_alpha_0002 x y dv_x_y)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb094_split_alpha_0003 x y)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb094_split_alpha_0003 x y))))))))))))) (TAlphaWff.conj
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb094_alpha_dummy_000) ≠ (nb094_alpha_dummy_002) from (by
                              unfold nb094_alpha_dummy_002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0006) 0))))
                          (show x ≠ (nb094_alpha_dummy_003 x y) from (by
                              unfold nb094_alpha_dummy_003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0007 x y) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.refl_of_closed
                        [((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)),
                          ((nb094_alpha_dummy_001), y), ((nb094_alpha_dummy_000), x),
                          ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
                        (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_002) from (by
                              unfold nb094_alpha_dummy_002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0042) 0))))
                          (show y ≠ (nb094_alpha_dummy_003 x y) from (by
                              unfold nb094_alpha_dummy_003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0043 x y) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb094_alpha_dummy_002), (nb094_alpha_dummy_003 x y)),
                          ((nb094_alpha_dummy_001), y), ((nb094_alpha_dummy_000), x),
                          ((nb094_alpha_dummy_004), (nb094_alpha_dummy_005 x y))]
                        (syn_cvv) (by simp only [fv_syn_cvv]))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb094_alpha_dummy_000) ≠
        (nb094_alpha_dummy_080) from (by
          unfold nb094_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0094) 0)))) (show x ≠ (nb094_alpha_dummy_081 x y) from (by
          unfold nb094_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0095 x y) 0)))) (TAlphaVar.there (show
        (nb094_alpha_dummy_000) ≠ (nb094_alpha_dummy_078) from (by
          unfold nb094_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0092) 0)))) (show x ≠ (nb094_alpha_dummy_079 x y) from (by
          unfold nb094_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0093 x y) 0)))) (TAlphaVar.there (show
        (nb094_alpha_dummy_000) ≠ (nb094_alpha_dummy_002) from (by
          unfold nb094_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0006) 0)))) (show x ≠ (nb094_alpha_dummy_003 x y) from (by
          unfold nb094_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_082) from (by
          unfold nb094_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094_alpha_dummy_083 y) from (by
          unfold nb094_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_080)
        from (by
          unfold nb094_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094_alpha_dummy_081 x y) from (by
          unfold nb094_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_078)
        from (by
          unfold nb094_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094_alpha_dummy_079 x y) from (by
          unfold nb094_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_002)
        from (by
          unfold nb094_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094_alpha_dummy_003 x y) from (by
          unfold nb094_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_082) from (by
          unfold nb094_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094_alpha_dummy_083 y) from (by
          unfold nb094_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_080)
        from (by
          unfold nb094_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094_alpha_dummy_081 x y) from (by
          unfold nb094_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_078)
        from (by
          unfold nb094_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094_alpha_dummy_079 x y) from (by
          unfold nb094_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_002)
        from (by
          unfold nb094_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094_alpha_dummy_003 x y) from (by
          unfold nb094_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb094_alpha_dummy_000) ≠
        (nb094_alpha_dummy_080) from (by
          unfold nb094_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0094) 0)))) (show x ≠ (nb094_alpha_dummy_081 x y) from (by
          unfold nb094_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0095 x y) 0)))) (TAlphaVar.there (show
        (nb094_alpha_dummy_000) ≠ (nb094_alpha_dummy_078) from (by
          unfold nb094_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0092) 0)))) (show x ≠ (nb094_alpha_dummy_079 x y) from (by
          unfold nb094_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0093 x y) 0)))) (TAlphaVar.there (show
        (nb094_alpha_dummy_000) ≠ (nb094_alpha_dummy_002) from (by
          unfold nb094_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0006) 0)))) (show x ≠ (nb094_alpha_dummy_003 x y) from (by
          unfold nb094_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_082) from (by
          unfold nb094_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094_alpha_dummy_083 y) from (by
          unfold nb094_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_080)
        from (by
          unfold nb094_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094_alpha_dummy_081 x y) from (by
          unfold nb094_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_078)
        from (by
          unfold nb094_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094_alpha_dummy_079 x y) from (by
          unfold nb094_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_002)
        from (by
          unfold nb094_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094_alpha_dummy_003 x y) from (by
          unfold nb094_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_082) from (by
          unfold nb094_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094_alpha_dummy_083 y) from (by
          unfold nb094_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_080)
        from (by
          unfold nb094_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094_alpha_dummy_081 x y) from (by
          unfold nb094_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_078)
        from (by
          unfold nb094_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094_alpha_dummy_079 x y) from (by
          unfold nb094_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094_alpha_dummy_001) ≠ (nb094_alpha_dummy_002)
        from (by
          unfold nb094_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094_alpha_dummy_003 x y) from (by
          unfold nb094_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
