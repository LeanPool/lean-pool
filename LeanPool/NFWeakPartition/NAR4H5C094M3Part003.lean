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

/-- Checked nominal proof certificate identified upstream as `nb094_split_alpha_0003`. -/
@[expose]
noncomputable def nb094SplitAlpha0003 (x : Var) (y : Var) :
    TAlphaWff
      [((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
        ((nb094AlphaDummy072), (nb094AlphaDummy073 x y)),
        ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
        ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
        ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy007))
          (Class.cv (nb094AlphaDummy002))) (Wff.neg
          (Wff.classEq (Class.cv (nb094AlphaDummy006))
            (synCun (synCphi (Class.cv (nb094AlphaDummy007))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb094AlphaDummy009 x y))
          (Class.cv (nb094AlphaDummy003 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb094AlphaDummy008 x y))
            (synCun (synCphi (Class.cv (nb094AlphaDummy009 x y)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy007) from (by
              unfold nb094AlphaDummy007;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 1))))
          (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy009 x y) from (by
              unfold nb094AlphaDummy009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 1))))
          (TAlphaVar.there (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy006) from (by
                unfold nb094AlphaDummy006;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0082) 0))))
            (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy008 x y) from (by
                unfold nb094AlphaDummy008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0084 x y) 0))))
            (TAlphaVar.there (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy072) from (by
                  unfold nb094AlphaDummy072;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0086) 0))))
              (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy073 x y) from (by
                  unfold nb094AlphaDummy073;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0087 x y) 0))))
              (TAlphaVar.there (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy010) from (by
                    unfold nb094AlphaDummy010;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0083) 0))))
                (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy011 x y) from (by
                    unfold nb094AlphaDummy011;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb094_support_mem_0085 x y) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((synCop (Class.cv (nb094AlphaDummy000))
                    (Class.cv (nb094AlphaDummy001)))).fv ∪
                ((Class.cv (nb094AlphaDummy002))).fv) (by decide)) (freshVar_injective
              (((synCop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb094AlphaDummy003 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy007) ≠ (nb094AlphaDummy050) from (by
                                        unfold nb094AlphaDummy050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0060)
                                                0)))) (show (nb094AlphaDummy009 x y) ≠
                                        (nb094AlphaDummy052 x y) from (by
                                        unfold nb094AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0061 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb094AlphaDummy007) ≠ (nb094AlphaDummy051) from
                                        (by
                                          unfold nb094AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0060)
                                                  1)))) (show (nb094AlphaDummy009 x y) ≠
        (nb094AlphaDummy053 x y) from (by
                                          unfold nb094AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0061 x y) 1))))
                                      (TAlphaVar.there (show (nb094AlphaDummy007) ≠
        (nb094AlphaDummy076) from (by
          unfold nb094AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0090) 0)))) (show (nb094AlphaDummy009 x y) ≠
        (nb094AlphaDummy077 x y) from (by
          unfold nb094AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0091 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy007) ≠ (nb094AlphaDummy074) from (by
          unfold nb094AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0088) 0)))) (show (nb094AlphaDummy009 x y) ≠
        (nb094AlphaDummy075 x y) from (by
          unfold nb094AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0089 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb094AlphaDummy007))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb094AlphaDummy009 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy057) from (by
          unfold nb094AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  1)))) (show (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy060 x y) from (by
          unfold nb094AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy056)
        from (by
          unfold nb094AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  0)))) (show (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy059 x y) from (by
          unfold nb094AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054)
        from (by
          unfold
            nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062)
                  0)))) (show (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy055 x y) from (by
          unfold
            nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
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
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠
        (nb094AlphaDummy068) from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠
        (nb094AlphaDummy068) from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054)
        from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb094AlphaDummy007) ≠ (nb094AlphaDummy050) from (by
                                        unfold nb094AlphaDummy050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb094_support_mem_0060)
                                                0)))) (show (nb094AlphaDummy009 x y) ≠
                                        (nb094AlphaDummy052 x y) from (by
                                        unfold nb094AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb094_support_mem_0061 x y) 0))))
                                    (TAlphaVar.there (show
                                        (nb094AlphaDummy007) ≠ (nb094AlphaDummy051) from
                                        (by
                                          unfold nb094AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb094_support_mem_0060)
                                                  1)))) (show (nb094AlphaDummy009 x y) ≠
        (nb094AlphaDummy053 x y) from (by
                                          unfold nb094AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb094_support_mem_0061 x y) 1))))
                                      (TAlphaVar.there (show (nb094AlphaDummy007) ≠
        (nb094AlphaDummy076) from (by
          unfold nb094AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0090) 0)))) (show (nb094AlphaDummy009 x y) ≠
        (nb094AlphaDummy077 x y) from (by
          unfold nb094AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0091 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy007) ≠ (nb094AlphaDummy074) from (by
          unfold nb094AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0088) 0)))) (show (nb094AlphaDummy009 x y) ≠
        (nb094AlphaDummy075 x y) from (by
          unfold nb094AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0089 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb094AlphaDummy007))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb094AlphaDummy009 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy057) from (by
          unfold nb094AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  1)))) (show (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy060 x y) from (by
          unfold nb094AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  1)))) (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy056)
        from (by
          unfold nb094AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0064)
                  0)))) (show (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy059 x y) from (by
          unfold nb094AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054)
        from (by
          unfold
            nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062)
                  0)))) (show (nb094AlphaDummy052 x y) ≠ (nb094AlphaDummy055 x y) from (by
          unfold
            nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
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
        (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0068)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0066)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy064) from (by
          unfold
            nb094AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0072)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy065 x y) from (by
          unfold
            nb094AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0073
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy062)
        from (by
          unfold
            nb094AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0070)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy063 x y) from (by
          unfold
            nb094AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0071
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy058), (nb094AlphaDummy061 x y)), ((nb094AlphaDummy057),
        (nb094AlphaDummy060 x y)), ((nb094AlphaDummy056), (nb094AlphaDummy059 x y)),
        ((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb094AlphaDummy050))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052
        x y))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠
        (nb094AlphaDummy068) from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy057) ≠
        (nb094AlphaDummy068) from (by
          unfold
            nb094AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0076)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy069 x y) from (by
          unfold
            nb094AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0077
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy057) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0074)
                  0)))) (show (nb094AlphaDummy060 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0075
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb094AlphaDummy050))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb094AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy058) ≠
        (nb094AlphaDummy070) from (by
          unfold
            nb094AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0080)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy071 x y) from (by
          unfold
            nb094AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0081
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy058) ≠ (nb094AlphaDummy066)
        from (by
          unfold
            nb094AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0078)
                  0)))) (show (nb094AlphaDummy061 x y) ≠ (nb094AlphaDummy067 x y) from (by
          unfold
            nb094AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0079
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054)
        from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb094AlphaDummy050) ≠ (nb094AlphaDummy054) from (by
          unfold nb094AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0062) 0)))) (show (nb094AlphaDummy052 x y) ≠
        (nb094AlphaDummy055 x y) from (by
          unfold nb094AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0063 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb094AlphaDummy054), (nb094AlphaDummy055 x y)), ((nb094AlphaDummy050),
        (nb094AlphaDummy052 x y)), ((nb094AlphaDummy051), (nb094AlphaDummy053 x y)),
        ((nb094AlphaDummy076), (nb094AlphaDummy077 x y)), ((nb094AlphaDummy074),
        (nb094AlphaDummy075 x y)), ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
        ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)), ((nb094AlphaDummy072),
        (nb094AlphaDummy073 x y)), ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
        ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)), ((nb094AlphaDummy001), y),
        ((nb094AlphaDummy000), x), ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb094AlphaDummy074), (nb094AlphaDummy075 x y)),
                    ((nb094AlphaDummy007), (nb094AlphaDummy009 x y)),
                    ((nb094AlphaDummy006), (nb094AlphaDummy008 x y)),
                    ((nb094AlphaDummy072), (nb094AlphaDummy073 x y)),
                    ((nb094AlphaDummy010), (nb094AlphaDummy011 x y)),
                    ((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                    ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                    ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_lndifop`. -/
@[expose]
noncomputable def nominalDfLndifop (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synClndifop)
        (synCmpt2 x (synCvv) y (synCvv) (synCdif (.cv x) (.cv y)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (show (nb094AlphaDummy002) ≠ (nb094AlphaDummy004) from (by
                            unfold nb094AlphaDummy004;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0004) 0))))) (Ne.symm
                        (show (nb094AlphaDummy003 x y) ≠ (nb094AlphaDummy005 x y) from (by
                            unfold nb094AlphaDummy005;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb094_support_mem_0005 x y) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy004) from (by
                              unfold nb094AlphaDummy004;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0002) 0))))) (Ne.symm
                          (show y ≠ (nb094AlphaDummy005 x y) from (by
                              unfold nb094AlphaDummy005;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0003 x y) 0)))))
                        (TAlphaVar.there (Ne.symm
                            (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy004) from (by
                                unfold nb094AlphaDummy004;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0000) 0))))) (Ne.symm
                            (show x ≠ (nb094AlphaDummy005 x y) from (by
                                unfold nb094AlphaDummy005;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb094_support_mem_0001 x y) 0)))))
                          (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb094SplitAlpha0002 x y dv_x_y)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb094SplitAlpha0003 x y)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb094SplitAlpha0003 x y))))))))))))) (TAlphaWff.conj
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb094AlphaDummy000) ≠ (nb094AlphaDummy002) from (by
                              unfold nb094AlphaDummy002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0006) 0))))
                          (show x ≠ (nb094AlphaDummy003 x y) from (by
                              unfold nb094AlphaDummy003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0007 x y) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.reflOfClosed
                        [((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                          ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                          ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                        (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002) from (by
                              unfold nb094AlphaDummy002;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0042) 0))))
                          (show y ≠ (nb094AlphaDummy003 x y) from (by
                              unfold nb094AlphaDummy003;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb094_support_mem_0043 x y) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb094AlphaDummy002), (nb094AlphaDummy003 x y)),
                          ((nb094AlphaDummy001), y), ((nb094AlphaDummy000), x),
                          ((nb094AlphaDummy004), (nb094AlphaDummy005 x y))]
                        (synCvv) (by simp only [fv_syn_cvv]))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb094AlphaDummy000) ≠
        (nb094AlphaDummy080) from (by
          unfold nb094AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0094) 0)))) (show x ≠ (nb094AlphaDummy081 x y) from (by
          unfold nb094AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0095 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy000) ≠ (nb094AlphaDummy078) from (by
          unfold nb094AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0092) 0)))) (show x ≠ (nb094AlphaDummy079 x y) from (by
          unfold nb094AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0093 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy000) ≠ (nb094AlphaDummy002) from (by
          unfold nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0006) 0)))) (show x ≠ (nb094AlphaDummy003 x y) from (by
          unfold nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy082) from (by
          unfold nb094AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094AlphaDummy083 y) from (by
          unfold nb094AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy080)
        from (by
          unfold nb094AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094AlphaDummy081 x y) from (by
          unfold nb094AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy078)
        from (by
          unfold nb094AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094AlphaDummy079 x y) from (by
          unfold nb094AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy082) from (by
          unfold nb094AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094AlphaDummy083 y) from (by
          unfold nb094AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy080)
        from (by
          unfold nb094AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094AlphaDummy081 x y) from (by
          unfold nb094AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy078)
        from (by
          unfold nb094AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094AlphaDummy079 x y) from (by
          unfold nb094AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold nb094AlphaDummy003;
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
                                      (TAlphaVar.there (show (nb094AlphaDummy000) ≠
        (nb094AlphaDummy080) from (by
          unfold nb094AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0094) 0)))) (show x ≠ (nb094AlphaDummy081 x y) from (by
          unfold nb094AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0095 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy000) ≠ (nb094AlphaDummy078) from (by
          unfold nb094AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0092) 0)))) (show x ≠ (nb094AlphaDummy079 x y) from (by
          unfold nb094AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0093 x y) 0)))) (TAlphaVar.there (show
        (nb094AlphaDummy000) ≠ (nb094AlphaDummy002) from (by
          unfold nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0006) 0)))) (show x ≠ (nb094AlphaDummy003 x y) from (by
          unfold nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy082) from (by
          unfold nb094AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094AlphaDummy083 y) from (by
          unfold nb094AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy080)
        from (by
          unfold nb094AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094AlphaDummy081 x y) from (by
          unfold nb094AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy078)
        from (by
          unfold nb094AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094AlphaDummy079 x y) from (by
          unfold nb094AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb094AlphaDummy001) ≠ (nb094AlphaDummy082) from (by
          unfold nb094AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0100) 0)))) (show y ≠ (nb094AlphaDummy083 y) from (by
          unfold nb094AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0101 y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy080)
        from (by
          unfold nb094AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0098)
                  0)))) (show y ≠ (nb094AlphaDummy081 x y) from (by
          unfold nb094AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0099 x y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy078)
        from (by
          unfold nb094AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0096)
                  0)))) (show y ≠ (nb094AlphaDummy079 x y) from (by
          unfold nb094AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0097 x
                    y)
                  0)))) (TAlphaVar.there (show (nb094AlphaDummy001) ≠ (nb094AlphaDummy002)
        from (by
          unfold nb094AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0042)
                  0)))) (show y ≠ (nb094AlphaDummy003 x y) from (by
          unfold nb094AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb094_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
