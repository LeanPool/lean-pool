/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR092FirstProof


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

/-- Checked nominal proof certificate identified upstream as `nb092_split_alpha_0001`. -/
@[expose]
noncomputable def nb092SplitAlpha0001 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)),
        ((nb092AlphaDummy072 R), (nb092AlphaDummy073 x y)),
        ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb092AlphaDummy043 R))
          (Class.cv (nb092AlphaDummy003 R))) (Wff.neg
          (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
            (synCun (synCphi (Class.cv (nb092AlphaDummy043 R))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb092AlphaDummy045 x y)) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
            (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy043 R) from (by
              unfold nb092AlphaDummy043;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 1))))
          (show y ≠ (nb092AlphaDummy045 x y) from (by
              unfold nb092AlphaDummy045;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 1))))
          (TAlphaVar.there (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy042 R) from (by
                unfold nb092AlphaDummy042;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 0))))
            (show y ≠ (nb092AlphaDummy044 x y) from (by
                unfold nb092AlphaDummy044;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 0))))
            (TAlphaVar.there (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy072 R) from
                (by
                  unfold nb092AlphaDummy072;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0074 R) 0))))
              (show y ≠ (nb092AlphaDummy073 x y) from (by
                  unfold nb092AlphaDummy073;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0075 x y) 0))))
              (TAlphaVar.there (show (nb092AlphaDummy003 R) ≠ (nb092AlphaDummy046 R) from
                  (by
                    unfold nb092AlphaDummy046;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0071 R) 0))))
                (show y ≠ (nb092AlphaDummy047 x y) from (by
                    unfold nb092AlphaDummy047;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0073 x y) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy002 R))).fv ∪
                ((Class.cv (nb092AlphaDummy003 R))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy050 R) from
                                      (by
                                        unfold nb092AlphaDummy050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0048 R)
                                                0)))) (show (nb092AlphaDummy045 x y) ≠
                                        (nb092AlphaDummy052 x y) from (by
                                        unfold nb092AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0049 x y) 0))))
                                    (TAlphaVar.there (show (nb092AlphaDummy043 R) ≠
        (nb092AlphaDummy051 R) from (by
                                          unfold nb092AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0048 R) 1)))) (show
                                        (nb092AlphaDummy045 x y) ≠
        (nb092AlphaDummy053 x y) from (by
                                          unfold nb092AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0049 x y) 1))))
                                      (TAlphaVar.there (show (nb092AlphaDummy043 R) ≠
        (nb092AlphaDummy076 R) from (by
          unfold nb092AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0078 R) 0)))) (show (nb092AlphaDummy045 x y) ≠
        (nb092AlphaDummy077 x y) from (by
          unfold nb092AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0079 x y) 0)))) (TAlphaVar.there (show
        (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy074 R) from (by
          unfold nb092AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0076 R) 0)))) (show (nb092AlphaDummy045 x y) ≠
        (nb092AlphaDummy075 x y) from (by
          unfold nb092AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0077 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb092AlphaDummy043 R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb092AlphaDummy045 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy057 R) from (by
          unfold nb092AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052
                    R)
                  1)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy060 x y) from (by
          unfold nb092AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053
                    x y)
                  1)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy056 R) from (by
          unfold nb092AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy059 x y) from (by
          unfold nb092AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold
            nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy055 x y) from (by
          unfold
            nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057
        R) ≠ (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy050 R) from
                                      (by
                                        unfold nb092AlphaDummy050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0048 R)
                                                0)))) (show (nb092AlphaDummy045 x y) ≠
                                        (nb092AlphaDummy052 x y) from (by
                                        unfold nb092AlphaDummy052;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0049 x y) 0))))
                                    (TAlphaVar.there (show (nb092AlphaDummy043 R) ≠
        (nb092AlphaDummy051 R) from (by
                                          unfold nb092AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0048 R) 1)))) (show
                                        (nb092AlphaDummy045 x y) ≠
        (nb092AlphaDummy053 x y) from (by
                                          unfold nb092AlphaDummy053;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb092_support_mem_0049 x y) 1))))
                                      (TAlphaVar.there (show (nb092AlphaDummy043 R) ≠
        (nb092AlphaDummy076 R) from (by
          unfold nb092AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0078 R) 0)))) (show (nb092AlphaDummy045 x y) ≠
        (nb092AlphaDummy077 x y) from (by
          unfold nb092AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0079 x y) 0)))) (TAlphaVar.there (show
        (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy074 R) from (by
          unfold nb092AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0076 R) 0)))) (show (nb092AlphaDummy045 x y) ≠
        (nb092AlphaDummy075 x y) from (by
          unfold nb092AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0077 x y) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb092AlphaDummy043 R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb092AlphaDummy045 x y))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy057 R) from (by
          unfold nb092AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052
                    R)
                  1)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy060 x y) from (by
          unfold nb092AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053
                    x y)
                  1)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy056 R) from (by
          unfold nb092AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy059 x y) from (by
          unfold nb092AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold
            nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy055 x y) from (by
          unfold
            nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057
        R) ≠ (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy076 R), (nb092AlphaDummy077 x y)), ((nb092AlphaDummy074 R),
        (nb092AlphaDummy075 x y)), ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
        ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)), ((nb092AlphaDummy072 R),
        (nb092AlphaDummy073 x y)), ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb092AlphaDummy074 R), (nb092AlphaDummy075 x y)),
                    ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)),
                    ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)),
                    ((nb092AlphaDummy072 R), (nb092AlphaDummy073 x y)),
                    ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
                    ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
                    ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
                    ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb092_split_alpha_0002`. -/
@[expose]
noncomputable def nb092SplitAlpha0002 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb092AlphaDummy046 R)) (synCcompl
            (Class.cab (nb092AlphaDummy042 R)
              (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy002 R))
                (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                  (synCphi (Class.cv (nb092AlphaDummy043 R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb092AlphaDummy046 R)) (synCcompl
              (Class.cab (nb092AlphaDummy042 R)
                (synWrex (nb092AlphaDummy043 R) (Class.cv (nb092AlphaDummy003 R))
                  (Wff.classEq (Class.cv (nb092AlphaDummy042 R))
                    (synCun (synCphi (Class.cv (nb092AlphaDummy043 R)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb092AlphaDummy047 x y)) (synCcompl
            (Class.cab (nb092AlphaDummy044 x y)
              (synWrex (nb092AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                  (synCphi (Class.cv (nb092AlphaDummy045 x y)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb092AlphaDummy047 x y)) (synCcompl
              (Class.cab (nb092AlphaDummy044 x y)
                (synWrex (nb092AlphaDummy045 x y) (Class.cv y)
                  (Wff.classEq (Class.cv (nb092AlphaDummy044 x y))
                    (synCun (synCphi (Class.cv (nb092AlphaDummy045 x y)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy043 R) from (by
                              unfold nb092AlphaDummy043;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb092_support_mem_0042 R) 1))))
                          (show x ≠ (nb092AlphaDummy045 x y) from (by
                              unfold nb092AlphaDummy045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb092_support_mem_0044 x y) 1))))
                          (TAlphaVar.there
                            (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy042 R) from (by
                                unfold nb092AlphaDummy042;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb092_support_mem_0042 R) 0))))
                            (show x ≠ (nb092AlphaDummy044 x y) from (by
                                unfold nb092AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb092_support_mem_0044 x y) 0))))
                            (TAlphaVar.there
                              (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy048 R) from
                                (by
                                  unfold nb092AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb092_support_mem_0046 R) 0))))
                              (show x ≠ (nb092AlphaDummy049 x y) from (by
                                  unfold nb092AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb092_support_mem_0047 x y)
                                          0)))) (TAlphaVar.there (show
                                  (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy046 R) from (by
                                    unfold nb092AlphaDummy046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb092_support_mem_0043 R)
                                            0)))) (show x ≠ (nb092AlphaDummy047 x y) from (by
                                    unfold nb092AlphaDummy047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb092_support_mem_0045 x y)
                                            0))))
                                (TAlphaVar.there (freshVar_injective ((R).fv) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb092AlphaDummy002 R))).fv ∪
                              ((Class.cv (nb092AlphaDummy003 R))).fv) (by decide))
                          (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy050 R) from
                                    (by
                                      unfold nb092AlphaDummy050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0048 R)
                                              0)))) (show (nb092AlphaDummy045 x y) ≠
                                      (nb092AlphaDummy052 x y) from (by
                                      unfold nb092AlphaDummy052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0049 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy051 R) from
                                      (by
                                        unfold nb092AlphaDummy051;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0048 R)
                                                1)))) (show (nb092AlphaDummy045 x y) ≠
                                        (nb092AlphaDummy053 x y) from (by
                                        unfold nb092AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0049 x y) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb092AlphaDummy043 R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb092AlphaDummy045 x y))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy057 R) from (by
          unfold nb092AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052 R)
                  1)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy060 x y) from (by
          unfold nb092AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053 x
                    y)
                  1)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy056 R) from (by
          unfold nb092AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy059 x y) from (by
          unfold nb092AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R),
        (nb092AlphaDummy044 x y)), ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)),
        ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R),
        (nb092AlphaDummy044 x y)), ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)),
        ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057
        R) ≠ (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb092AlphaDummy054 R),
        (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R), (nb092AlphaDummy052 x y)),
        ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)), ((nb092AlphaDummy043 R),
        (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)),
        ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)), ((nb092AlphaDummy046 R),
        (nb092AlphaDummy047 x y)), ((nb092AlphaDummy003 R), y),
        ((nb092AlphaDummy002 R), x), ((nb092AlphaDummy001 R), b),
        ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R),
        (nb092AlphaDummy005 x y R a b))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb092AlphaDummy054 R),
        (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R), (nb092AlphaDummy052 x y)),
        ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)), ((nb092AlphaDummy043 R),
        (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)),
        ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)), ((nb092AlphaDummy046 R),
        (nb092AlphaDummy047 x y)), ((nb092AlphaDummy003 R), y),
        ((nb092AlphaDummy002 R), x), ((nb092AlphaDummy001 R), b),
        ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R),
        (nb092AlphaDummy005 x y R a b))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy043 R) from (by
                              unfold nb092AlphaDummy043;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb092_support_mem_0042 R) 1))))
                          (show x ≠ (nb092AlphaDummy045 x y) from (by
                              unfold nb092AlphaDummy045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb092_support_mem_0044 x y) 1))))
                          (TAlphaVar.there
                            (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy042 R) from (by
                                unfold nb092AlphaDummy042;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb092_support_mem_0042 R) 0))))
                            (show x ≠ (nb092AlphaDummy044 x y) from (by
                                unfold nb092AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb092_support_mem_0044 x y) 0))))
                            (TAlphaVar.there
                              (show (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy048 R) from
                                (by
                                  unfold nb092AlphaDummy048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb092_support_mem_0046 R) 0))))
                              (show x ≠ (nb092AlphaDummy049 x y) from (by
                                  unfold nb092AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb092_support_mem_0047 x y)
                                          0)))) (TAlphaVar.there (show
                                  (nb092AlphaDummy002 R) ≠ (nb092AlphaDummy046 R) from (by
                                    unfold nb092AlphaDummy046;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb092_support_mem_0043 R)
                                            0)))) (show x ≠ (nb092AlphaDummy047 x y) from (by
                                    unfold nb092AlphaDummy047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb092_support_mem_0045 x y)
                                            0))))
                                (TAlphaVar.there (freshVar_injective ((R).fv) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb092AlphaDummy002 R))).fv ∪
                              ((Class.cv (nb092AlphaDummy003 R))).fv) (by decide))
                          (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy050 R) from
                                    (by
                                      unfold nb092AlphaDummy050;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0048 R)
                                              0)))) (show (nb092AlphaDummy045 x y) ≠
                                      (nb092AlphaDummy052 x y) from (by
                                      unfold nb092AlphaDummy052;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb092_support_mem_0049 x y)
                                              0)))) (TAlphaVar.there (show
                                      (nb092AlphaDummy043 R) ≠ (nb092AlphaDummy051 R) from
                                      (by
                                        unfold nb092AlphaDummy051;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb092_support_mem_0048 R)
                                                1)))) (show (nb092AlphaDummy045 x y) ≠
                                        (nb092AlphaDummy053 x y) from (by
                                        unfold nb092AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb092_support_mem_0049 x y) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb092AlphaDummy043 R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb092AlphaDummy045 x y))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy057 R) from (by
          unfold nb092AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052 R)
                  1)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy060 x y) from (by
          unfold nb092AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053 x
                    y)
                  1)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy056 R) from (by
          unfold nb092AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0052
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy059 x y) from (by
          unfold nb092AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050
                    R)
                  0)))) (show (nb092AlphaDummy052 x y) ≠ (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R),
        (nb092AlphaDummy044 x y)), ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)),
        ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0056
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0057
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0054
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy064 R) from (by
          unfold
            nb092AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0060
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy065 x y) from (by
          unfold
            nb092AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0061
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy062 R) from (by
          unfold
            nb092AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0058
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy063 x y) from (by
          unfold
            nb092AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0059
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb092AlphaDummy058 R), (nb092AlphaDummy061 x y)), ((nb092AlphaDummy057 R),
        (nb092AlphaDummy060 x y)), ((nb092AlphaDummy056 R), (nb092AlphaDummy059 x y)),
        ((nb092AlphaDummy054 R), (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R),
        (nb092AlphaDummy052 x y)), ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)),
        ((nb092AlphaDummy043 R), (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R),
        (nb092AlphaDummy044 x y)), ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)),
        ((nb092AlphaDummy046 R), (nb092AlphaDummy047 x y)),
        ((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb092AlphaDummy050 R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb092AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy057
        R) ≠ (nb092AlphaDummy068 R) from (by
          unfold
            nb092AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0064
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy069 x y) from (by
          unfold
            nb092AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0065
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy057 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0062
                    R)
                  0)))) (show (nb092AlphaDummy060 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0063
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb092AlphaDummy050
        R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb092AlphaDummy052 x y))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb092AlphaDummy058
        R) ≠ (nb092AlphaDummy070 R) from (by
          unfold
            nb092AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0068
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy071 x y) from (by
          unfold
            nb092AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0069
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb092AlphaDummy058 R) ≠
        (nb092AlphaDummy066 R) from (by
          unfold
            nb092AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0066
                    R)
                  0)))) (show (nb092AlphaDummy061 x y) ≠ (nb092AlphaDummy067 x y) from (by
          unfold
            nb092AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0067
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb092AlphaDummy054 R),
        (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R), (nb092AlphaDummy052 x y)),
        ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)), ((nb092AlphaDummy043 R),
        (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)),
        ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)), ((nb092AlphaDummy046 R),
        (nb092AlphaDummy047 x y)), ((nb092AlphaDummy003 R), y),
        ((nb092AlphaDummy002 R), x), ((nb092AlphaDummy001 R), b),
        ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R),
        (nb092AlphaDummy005 x y R a b))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb092AlphaDummy050 R) ≠
        (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb092AlphaDummy050 R) ≠ (nb092AlphaDummy054 R) from (by
          unfold nb092AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0050 R) 0)))) (show (nb092AlphaDummy052 x y) ≠
        (nb092AlphaDummy055 x y) from (by
          unfold nb092AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb092_support_mem_0051 x y) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb092AlphaDummy054 R),
        (nb092AlphaDummy055 x y)), ((nb092AlphaDummy050 R), (nb092AlphaDummy052 x y)),
        ((nb092AlphaDummy051 R), (nb092AlphaDummy053 x y)), ((nb092AlphaDummy043 R),
        (nb092AlphaDummy045 x y)), ((nb092AlphaDummy042 R), (nb092AlphaDummy044 x y)),
        ((nb092AlphaDummy048 R), (nb092AlphaDummy049 x y)), ((nb092AlphaDummy046 R),
        (nb092AlphaDummy047 x y)), ((nb092AlphaDummy003 R), y),
        ((nb092AlphaDummy002 R), x), ((nb092AlphaDummy001 R), b),
        ((nb092AlphaDummy000 R), a), ((nb092AlphaDummy004 R),
        (nb092AlphaDummy005 x y R a b))] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb092SplitAlpha0001 x y R a b)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb092SplitAlpha0001 x y R a b)))))))))))

theorem nb092_focused_notmem_0000 (R : Class) : (nb092AlphaDummy003 R) ∉ R.fv :=
  by
  change freshVar ((R).fv) 3 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 3
      (fun _ hu => hu)

theorem nb092_focused_notmem_0001 (R : Class) : (nb092AlphaDummy002 R) ∉ R.fv :=
  by
  change freshVar ((R).fv) 2 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu => hu)

theorem nb092_focused_notmem_0002 (R : Class) : (nb092AlphaDummy001 R) ∉ R.fv :=
  by
  change freshVar ((R).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => hu)

theorem nb092_focused_notmem_0003 (R : Class) : (nb092AlphaDummy000 R) ∉ R.fv :=
  by
  change freshVar ((R).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => hu)

theorem nb092_focused_notmem_0004 (R : Class) : (nb092AlphaDummy004 R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb092AlphaDummy000 R)} : Finset Var) ∪
            ({(nb092AlphaDummy001 R)} : Finset Var) ∪
          ((synWrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
              (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
                (synWbr (Class.cv (nb092AlphaDummy002 R)) R
                  (Class.cv (nb092AlphaDummy003 R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wrex (nb092AlphaDummy002 R) (Class.cv (nb092AlphaDummy000 R))
      (synWrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
        (synWbr (Class.cv (nb092AlphaDummy002 R)) R (Class.cv (nb092AlphaDummy003 R))))]
  rw [Finset.mem_union]
  right
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb092_focused_notmem_0001 R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb092AlphaDummy003 R) (Class.cv (nb092AlphaDummy001 R))
        (synWbr (Class.cv (nb092AlphaDummy002 R)) R (Class.cv (nb092AlphaDummy003 R)))]
    rw [Finset.mem_union]
    right
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb092_focused_notmem_0000 R)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv (nb092AlphaDummy002 R)) R
          (Class.cv (nb092AlphaDummy003 R))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb092_focused_notmem_0005 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) : (nb092AlphaDummy005 x y R a b) ∉ R.fv :=
  by
  change
    freshVar
        (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((synWrex x (Class.cv a)
              (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wrex x (Class.cv a)
      (synWrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y)))]
  rw [Finset.mem_union]
  right
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => (dv_R_x) (h_eq ▸ hu)
  · rw [fv_syn_wrex y (Class.cv b) (synWbr (Class.cv x) R (Class.cv y))]
    rw [Finset.mem_union]
    right
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_R_y) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv x) R (Class.cv y)]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb092_compact_envfresh_0014 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var)
    (dv_R_a : a ∉ R.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TEnvFresh
      [((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb092AlphaDummy003 R) y (nb092_focused_notmem_0000 R) dv_R_y
      (TEnvFresh.consFresh (nb092AlphaDummy002 R) x (nb092_focused_notmem_0001 R) dv_R_x
        (TEnvFresh.consFresh (nb092AlphaDummy001 R) b (nb092_focused_notmem_0002 R) dv_R_b
          (TEnvFresh.consFresh (nb092AlphaDummy000 R) a (nb092_focused_notmem_0003 R) dv_R_a
            (TEnvFresh.consFresh (nb092AlphaDummy004 R)
              (nb092AlphaDummy005 x y R a b) (nb092_focused_notmem_0004 R)
              (nb092_focused_notmem_0005 x y R a b dv_R_x dv_R_y) (TEnvFresh.nil R.fv))))))

/-- Checked nominal proof certificate identified upstream as `nb092_focused_refl_0000`. -/
@[expose]
noncomputable def nb092FocusedRefl0000 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) (dv_R_a : a ∉ R.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) :
    TReflOn
      [((nb092AlphaDummy003 R), y), ((nb092AlphaDummy002 R), x),
        ((nb092AlphaDummy001 R), b), ((nb092AlphaDummy000 R), a),
        ((nb092AlphaDummy004 R), (nb092AlphaDummy005 x y R a b))]
      R.fv :=
  TEnvFresh.reflOn (nb092_compact_envfresh_0014 x y R a b dv_R_a dv_R_b dv_R_x dv_R_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
