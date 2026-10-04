/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C096M3Part002

/-! NF weak partition development: NAR4H5C096M3Part003. -/


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

/-- Checked nominal proof certificate identified upstream as `nb096_split_alpha_0003`. -/
@[expose]
noncomputable def nb096SplitAlpha0003 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096AlphaDummy071 D R), (nb096AlphaDummy072 R q)),
        ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
        ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy071 D R))
          (Class.cab (nb096AlphaDummy065 D R)
            (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
              (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                (synCphi (Class.cv (nb096AlphaDummy066 D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy071 D R))
            (Class.cab (nb096AlphaDummy065 D R)
              (synWrex (nb096AlphaDummy066 D R) (Class.cv (nb096AlphaDummy052 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy065 D R))
                  (synCphi (Class.cv (nb096AlphaDummy066 D R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy072 R q))
          (Class.cab (nb096AlphaDummy067 R q)
            (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
              (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                (synCphi (Class.cv (nb096AlphaDummy068 R q))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy072 R q))
            (Class.cab (nb096AlphaDummy067 R q)
              (synWrex (nb096AlphaDummy068 R q) (Class.cv (nb096AlphaDummy054 R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy067 R q))
                  (synCphi (Class.cv (nb096AlphaDummy068 R q))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy066 D R) from (by
                      unfold nb096AlphaDummy066;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
                  (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy068 R q) from (by
                      unfold nb096AlphaDummy068;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0062 R q) 1)))) (TAlphaVar.there
                    (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy065 D R) from (by
                        unfold nb096AlphaDummy065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
                    (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy067 R q) from (by
                        unfold nb096AlphaDummy067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
                    (TAlphaVar.there
                      (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy071 D R) from (by
                          unfold nb096AlphaDummy071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0064 D R) 0))))
                      (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy072 R q) from (by
                          unfold nb096AlphaDummy072;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0065 R q) 0))))
                      (TAlphaVar.there
                        (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy069 D R) from (by
                            unfold nb096AlphaDummy069;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0061 D R) 0))))
                        (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy070 R q) from (by
                            unfold nb096AlphaDummy070;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0063 R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
                      ((Class.cv (nb096AlphaDummy051 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
                      ((Class.cv (nb096AlphaDummy053 R q))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy073 D R) from
                            (by
                              unfold nb096AlphaDummy073;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0066 D R) 0))))
                          (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy075 R q) from
                            (by
                              unfold nb096AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0067 R q) 0))))
                          (TAlphaVar.there (show
                              (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy074 D R) from (by
                                unfold nb096AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0066 D R) 1)))) (show
                              (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy076 R q) from (by
                                unfold nb096AlphaDummy076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0067 R q) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb096AlphaDummy066 D R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb096AlphaDummy068 R q))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy080 D R) from
        (by
          unfold nb096AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R) 1)))) (show (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy083 R q) from (by
          unfold nb096AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q) 1)))) (TAlphaVar.there (show
        (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy079 D R) from (by
          unfold nb096AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R)
                  0)))) (show (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy082 R q) from (by
          unfold nb096AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy077 D R) from (by
          unfold nb096AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R)
                  0)))) (show (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from (by
          unfold nb096AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy081 D R), (nb096AlphaDummy084 R q)),
        ((nb096AlphaDummy080 D R), (nb096AlphaDummy083 R q)),
        ((nb096AlphaDummy079 D R), (nb096AlphaDummy082 R q)),
        ((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
        ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
        ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
        ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
        ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
        ((nb096AlphaDummy071 D R), (nb096AlphaDummy072 R q)),
        ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
        ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy081 D R), (nb096AlphaDummy084 R q)),
        ((nb096AlphaDummy080 D R), (nb096AlphaDummy083 R q)),
        ((nb096AlphaDummy079 D R), (nb096AlphaDummy082 R q)),
        ((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
        ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
        ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
        ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
        ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
        ((nb096AlphaDummy071 D R), (nb096AlphaDummy072 R q)),
        ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
        ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy075 R
        q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy091 D R) from
        (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy091 D R) from
        (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081
        D R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081
        D R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R)
                                      from (by
                                        unfold nb096AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0068 D R) 0)))) (show
                                      (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q)
                                      from (by
                                        unfold nb096AlphaDummy078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0069 R q) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                                    ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
                                    ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
                                    ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
                                    ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
                                    ((nb096AlphaDummy071 D R), (nb096AlphaDummy072 R q)),
                                    ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
                                    ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
                                    ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
                                    ((nb096AlphaDummy049 D R),
                                      (nb096AlphaDummy050 D R q)),
                                    ((nb096AlphaDummy047 D R),
                                      (nb096AlphaDummy048 D R q)),
                                    ((nb096AlphaDummy045 D R),
                                      (nb096AlphaDummy046 D R q)),
                                    ((nb096AlphaDummy042 D R),
                                      (nb096AlphaDummy044 D R q)),
                                    ((nb096AlphaDummy041 D R),
                                      (nb096AlphaDummy043 D R q)),
                                    ((nb096AlphaDummy001 D R),
                                      (nb096AlphaDummy002 D R q)),
                                    ((nb096AlphaDummy000 D R), q),
                                    ((nb096AlphaDummy003 D R),
                                      (nb096AlphaDummy004 D R q))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R)
                                    from (by
                                      unfold nb096AlphaDummy077;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0068 D R)
                                              0)))) (show (nb096AlphaDummy075 R q) ≠
                                      (nb096AlphaDummy078 R q) from (by
                                      unfold nb096AlphaDummy078;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0069 R q)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R)
                                      from (by
                                        unfold nb096AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0068 D R) 0)))) (show
                                      (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q)
                                      from (by
                                        unfold nb096AlphaDummy078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0069 R q) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                                    ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
                                    ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
                                    ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
                                    ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
                                    ((nb096AlphaDummy071 D R), (nb096AlphaDummy072 R q)),
                                    ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
                                    ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
                                    ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
                                    ((nb096AlphaDummy049 D R),
                                      (nb096AlphaDummy050 D R q)),
                                    ((nb096AlphaDummy047 D R),
                                      (nb096AlphaDummy048 D R q)),
                                    ((nb096AlphaDummy045 D R),
                                      (nb096AlphaDummy046 D R q)),
                                    ((nb096AlphaDummy042 D R),
                                      (nb096AlphaDummy044 D R q)),
                                    ((nb096AlphaDummy041 D R),
                                      (nb096AlphaDummy043 D R q)),
                                    ((nb096AlphaDummy001 D R),
                                      (nb096AlphaDummy002 D R q)),
                                    ((nb096AlphaDummy000 D R), q),
                                    ((nb096AlphaDummy003 D R),
                                      (nb096AlphaDummy004 D R q))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy066 D R) from (by
                        unfold nb096AlphaDummy066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0060 D R) 1))))
                    (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy068 R q) from (by
                        unfold nb096AlphaDummy068;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0062 R q) 1))))
                    (TAlphaVar.there
                      (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy065 D R) from (by
                          unfold nb096AlphaDummy065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0060 D R) 0))))
                      (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy067 R q) from (by
                          unfold nb096AlphaDummy067;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0062 R q) 0))))
                      (TAlphaVar.there
                        (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy071 D R) from (by
                            unfold nb096AlphaDummy071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0064 D R) 0))))
                        (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy072 R q) from (by
                            unfold nb096AlphaDummy072;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0065 R q) 0))))
                        (TAlphaVar.there
                          (show (nb096AlphaDummy052 D R) ≠ (nb096AlphaDummy069 D R) from
                            (by
                              unfold nb096AlphaDummy069;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0061 D R) 0))))
                          (show (nb096AlphaDummy054 R q) ≠ (nb096AlphaDummy070 R q) from
                            (by
                              unfold nb096AlphaDummy070;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0063 R q) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
                        ((Class.cv (nb096AlphaDummy051 D R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb096AlphaDummy054 R q))).fv ∪
                        ((Class.cv (nb096AlphaDummy053 R q))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy073 D R) from (by
                                unfold nb096AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0066 D R) 0)))) (show
                              (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy075 R q) from (by
                                unfold nb096AlphaDummy075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0067 R q) 0))))
                            (TAlphaVar.there (show
                                (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy074 D R) from
                                (by
                                  unfold nb096AlphaDummy074;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0066 D R)
                                          1)))) (show
                                (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy076 R q) from
                                (by
                                  unfold nb096AlphaDummy076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0067 R q)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb096AlphaDummy066 D R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb096AlphaDummy068 R q))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy080 D R) from (by
          unfold nb096AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R)
                  1)))) (show (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy083 R q) from (by
          unfold nb096AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy079 D R) from (by
          unfold nb096AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R)
                  0)))) (show (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy082 R q) from (by
          unfold nb096AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy077 D R) from (by
          unfold nb096AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R)
                  0)))) (show (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from (by
          unfold nb096AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy081 D R), (nb096AlphaDummy084 R q)),
        ((nb096AlphaDummy080 D R), (nb096AlphaDummy083 R q)),
        ((nb096AlphaDummy079 D R), (nb096AlphaDummy082 R q)),
        ((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
        ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
        ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
        ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
        ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
        ((nb096AlphaDummy071 D R), (nb096AlphaDummy072 R q)),
        ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
        ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy081 D R), (nb096AlphaDummy084 R q)),
        ((nb096AlphaDummy080 D R), (nb096AlphaDummy083 R q)),
        ((nb096AlphaDummy079 D R), (nb096AlphaDummy082 R q)),
        ((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
        ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
        ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
        ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
        ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
        ((nb096AlphaDummy071 D R), (nb096AlphaDummy072 R q)),
        ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
        ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy075 R
        q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy091 D R) from
        (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy091 D R) from
        (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081
        D R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081
        D R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy077 D R) from (by
                                          unfold nb096AlphaDummy077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0068 D R) 0)))) (show
                                        (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy078 R q) from (by
                                          unfold nb096AlphaDummy078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0069 R q) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                                      ((nb096AlphaDummy073 D R),
                                        (nb096AlphaDummy075 R q)),
                                      ((nb096AlphaDummy074 D R),
                                        (nb096AlphaDummy076 R q)),
                                      ((nb096AlphaDummy066 D R),
                                        (nb096AlphaDummy068 R q)),
                                      ((nb096AlphaDummy065 D R),
                                        (nb096AlphaDummy067 R q)),
                                      ((nb096AlphaDummy071 D R),
                                        (nb096AlphaDummy072 R q)),
                                      ((nb096AlphaDummy069 D R),
                                        (nb096AlphaDummy070 R q)),
                                      ((nb096AlphaDummy052 D R),
                                        (nb096AlphaDummy054 R q)),
                                      ((nb096AlphaDummy051 D R),
                                        (nb096AlphaDummy053 R q)),
                                      ((nb096AlphaDummy049 D R),
                                        (nb096AlphaDummy050 D R q)),
                                      ((nb096AlphaDummy047 D R),
                                        (nb096AlphaDummy048 D R q)),
                                      ((nb096AlphaDummy045 D R),
                                        (nb096AlphaDummy046 D R q)),
                                      ((nb096AlphaDummy042 D R),
                                        (nb096AlphaDummy044 D R q)),
                                      ((nb096AlphaDummy041 D R),
                                        (nb096AlphaDummy043 D R q)),
                                      ((nb096AlphaDummy001 D R),
                                        (nb096AlphaDummy002 D R q)),
                                      ((nb096AlphaDummy000 D R), q),
                                      ((nb096AlphaDummy003 D R),
                                        (nb096AlphaDummy004 D R q))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R)
                                      from (by
                                        unfold nb096AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0068 D R) 0)))) (show
                                      (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q)
                                      from (by
                                        unfold nb096AlphaDummy078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0069 R q) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy077 D R) from (by
                                          unfold nb096AlphaDummy077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0068 D R) 0)))) (show
                                        (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy078 R q) from (by
                                          unfold nb096AlphaDummy078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0069 R q) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                                      ((nb096AlphaDummy073 D R),
                                        (nb096AlphaDummy075 R q)),
                                      ((nb096AlphaDummy074 D R),
                                        (nb096AlphaDummy076 R q)),
                                      ((nb096AlphaDummy066 D R),
                                        (nb096AlphaDummy068 R q)),
                                      ((nb096AlphaDummy065 D R),
                                        (nb096AlphaDummy067 R q)),
                                      ((nb096AlphaDummy071 D R),
                                        (nb096AlphaDummy072 R q)),
                                      ((nb096AlphaDummy069 D R),
                                        (nb096AlphaDummy070 R q)),
                                      ((nb096AlphaDummy052 D R),
                                        (nb096AlphaDummy054 R q)),
                                      ((nb096AlphaDummy051 D R),
                                        (nb096AlphaDummy053 R q)),
                                      ((nb096AlphaDummy049 D R),
                                        (nb096AlphaDummy050 D R q)),
                                      ((nb096AlphaDummy047 D R),
                                        (nb096AlphaDummy048 D R q)),
                                      ((nb096AlphaDummy045 D R),
                                        (nb096AlphaDummy046 D R q)),
                                      ((nb096AlphaDummy042 D R),
                                        (nb096AlphaDummy044 D R q)),
                                      ((nb096AlphaDummy041 D R),
                                        (nb096AlphaDummy043 D R q)),
                                      ((nb096AlphaDummy001 D R),
                                        (nb096AlphaDummy002 D R q)),
                                      ((nb096AlphaDummy000 D R), q),
                                      ((nb096AlphaDummy003 D R),
                                        (nb096AlphaDummy004 D R q))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb096_split_alpha_0004`. -/
@[expose]
noncomputable def nb096SplitAlpha0004 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096AlphaDummy099 D R), (nb096AlphaDummy100 R q)),
        ((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)),
        ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
        ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
        ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)),
        ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
        ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy099 D R))
          (synCphi (Class.cv (nb096AlphaDummy066 D R)))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy099 D R))
            (synCphi (Class.cv (nb096AlphaDummy066 D R))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy100 R q))
          (synCphi (Class.cv (nb096AlphaDummy068 R q)))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy100 R q))
            (synCphi (Class.cv (nb096AlphaDummy068 R q)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy073 D R) from (by
                      unfold nb096AlphaDummy073;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0066 D R) 0))))
                  (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy075 R q) from (by
                      unfold nb096AlphaDummy075;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb096_support_mem_0067 R q) 0)))) (TAlphaVar.there
                    (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy074 D R) from (by
                        unfold nb096AlphaDummy074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0066 D R) 1))))
                    (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy076 R q) from (by
                        unfold nb096AlphaDummy076;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0067 R q) 1))))
                    (TAlphaVar.there
                      (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy099 D R) from (by
                          unfold nb096AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0096 D R) 0))))
                      (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy100 R q) from (by
                          unfold nb096AlphaDummy100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0097 R q) 0))))
                      (TAlphaVar.there
                        (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy097 D R) from (by
                            unfold nb096AlphaDummy097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0094 D R) 0))))
                        (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy098 R q) from (by
                            unfold nb096AlphaDummy098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0095 R q) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb096AlphaDummy066 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb096AlphaDummy068 R q))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy080 D R)
                                      from (by
                                        unfold nb096AlphaDummy080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0070 D R) 1)))) (show
                                      (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy083 R q)
                                      from (by
                                        unfold nb096AlphaDummy083;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0071 R q) 1))))
                                    (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy079 D R) from (by
                                          unfold nb096AlphaDummy079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0070 D R) 0)))) (show
                                        (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy082 R q) from (by
                                          unfold nb096AlphaDummy082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0071 R q) 0))))
                                      (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy077 D R) from (by
          unfold nb096AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R) 0)))) (show (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy078 R q) from (by
          unfold nb096AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb096AlphaDummy081 D R),
        (nb096AlphaDummy084 R q)), ((nb096AlphaDummy080 D R),
        (nb096AlphaDummy083 R q)), ((nb096AlphaDummy079 D R),
        (nb096AlphaDummy082 R q)), ((nb096AlphaDummy077 D R),
        (nb096AlphaDummy078 R q)), ((nb096AlphaDummy073 D R),
        (nb096AlphaDummy075 R q)), ((nb096AlphaDummy074 D R),
        (nb096AlphaDummy076 R q)), ((nb096AlphaDummy099 D R),
        (nb096AlphaDummy100 R q)), ((nb096AlphaDummy097 D R),
        (nb096AlphaDummy098 R q)), ((nb096AlphaDummy066 D R),
        (nb096AlphaDummy068 R q)), ((nb096AlphaDummy065 D R),
        (nb096AlphaDummy067 R q)), ((nb096AlphaDummy095 D R),
        (nb096AlphaDummy096 R q)), ((nb096AlphaDummy069 D R),
        (nb096AlphaDummy070 R q)), ((nb096AlphaDummy052 D R),
        (nb096AlphaDummy054 R q)), ((nb096AlphaDummy051 D R),
        (nb096AlphaDummy053 R q)), ((nb096AlphaDummy049 D R),
        (nb096AlphaDummy050 D R q)), ((nb096AlphaDummy047 D R),
        (nb096AlphaDummy048 D R q)), ((nb096AlphaDummy045 D R),
        (nb096AlphaDummy046 D R q)), ((nb096AlphaDummy042 D R),
        (nb096AlphaDummy044 D R q)), ((nb096AlphaDummy041 D R),
        (nb096AlphaDummy043 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
                                        ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy087 D R) from (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy087 D R) from (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy087 D R) from (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb096AlphaDummy081 D R),
        (nb096AlphaDummy084 R q)), ((nb096AlphaDummy080 D R),
        (nb096AlphaDummy083 R q)), ((nb096AlphaDummy079 D R),
        (nb096AlphaDummy082 R q)), ((nb096AlphaDummy077 D R),
        (nb096AlphaDummy078 R q)), ((nb096AlphaDummy073 D R),
        (nb096AlphaDummy075 R q)), ((nb096AlphaDummy074 D R),
        (nb096AlphaDummy076 R q)), ((nb096AlphaDummy099 D R),
        (nb096AlphaDummy100 R q)), ((nb096AlphaDummy097 D R),
        (nb096AlphaDummy098 R q)), ((nb096AlphaDummy066 D R),
        (nb096AlphaDummy068 R q)), ((nb096AlphaDummy065 D R),
        (nb096AlphaDummy067 R q)), ((nb096AlphaDummy095 D R),
        (nb096AlphaDummy096 R q)), ((nb096AlphaDummy069 D R),
        (nb096AlphaDummy070 R q)), ((nb096AlphaDummy052 D R),
        (nb096AlphaDummy054 R q)), ((nb096AlphaDummy051 D R),
        (nb096AlphaDummy053 R q)), ((nb096AlphaDummy049 D R),
        (nb096AlphaDummy050 D R q)), ((nb096AlphaDummy047 D R),
        (nb096AlphaDummy048 D R q)), ((nb096AlphaDummy045 D R),
        (nb096AlphaDummy046 D R q)), ((nb096AlphaDummy042 D R),
        (nb096AlphaDummy044 D R q)), ((nb096AlphaDummy041 D R),
        (nb096AlphaDummy043 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy091 D R) from (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy091 D R) from (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R) from (by
                                unfold nb096AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)))) (show
                              (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from (by
                                unfold nb096AlphaDummy078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                            ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
                            ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
                            ((nb096AlphaDummy099 D R), (nb096AlphaDummy100 R q)),
                            ((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)),
                            ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
                            ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
                            ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)),
                            ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
                            ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
                            ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
                            ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
                            ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
                            ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
                            ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
                            ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
                            ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                            ((nb096AlphaDummy000 D R), q),
                            ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R) from
                            (by
                              unfold nb096AlphaDummy077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0068 D R) 0))))
                          (show (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from
                            (by
                              unfold nb096AlphaDummy078;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R) from (by
                                unfold nb096AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)))) (show
                              (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from (by
                                unfold nb096AlphaDummy078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                            ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
                            ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
                            ((nb096AlphaDummy099 D R), (nb096AlphaDummy100 R q)),
                            ((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)),
                            ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
                            ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
                            ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)),
                            ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
                            ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
                            ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
                            ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
                            ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
                            ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
                            ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
                            ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
                            ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                            ((nb096AlphaDummy000 D R), q),
                            ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy073 D R) from (by
                        unfold nb096AlphaDummy073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0066 D R) 0))))
                    (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy075 R q) from (by
                        unfold nb096AlphaDummy075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb096_support_mem_0067 R q) 0))))
                    (TAlphaVar.there
                      (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy074 D R) from (by
                          unfold nb096AlphaDummy074;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0066 D R) 1))))
                      (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy076 R q) from (by
                          unfold nb096AlphaDummy076;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0067 R q) 1))))
                      (TAlphaVar.there
                        (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy099 D R) from (by
                            unfold nb096AlphaDummy099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0096 D R) 0))))
                        (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy100 R q) from (by
                            unfold nb096AlphaDummy100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb096_support_mem_0097 R q) 0))))
                        (TAlphaVar.there
                          (show (nb096AlphaDummy066 D R) ≠ (nb096AlphaDummy097 D R) from
                            (by
                              unfold nb096AlphaDummy097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0094 D R) 0))))
                          (show (nb096AlphaDummy068 R q) ≠ (nb096AlphaDummy098 R q) from
                            (by
                              unfold nb096AlphaDummy098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0095 R q) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb096AlphaDummy066 D R))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb096AlphaDummy068 R q))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy080 D R) from (by
                                          unfold nb096AlphaDummy080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0070 D R) 1)))) (show
                                        (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy083 R q) from (by
                                          unfold nb096AlphaDummy083;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0071 R q) 1))))
                                      (TAlphaVar.there (show (nb096AlphaDummy073 D R) ≠
        (nb096AlphaDummy079 D R) from (by
          unfold nb096AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0070 D R) 0)))) (show (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy082 R q) from (by
          unfold nb096AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0071 R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R) from (by
          unfold nb096AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0068 D R) 0)))) (show (nb096AlphaDummy075 R q) ≠
        (nb096AlphaDummy078 R q) from (by
          unfold nb096AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0069 R q) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb096AlphaDummy081 D R),
        (nb096AlphaDummy084 R q)), ((nb096AlphaDummy080 D R),
        (nb096AlphaDummy083 R q)), ((nb096AlphaDummy079 D R),
        (nb096AlphaDummy082 R q)), ((nb096AlphaDummy077 D R),
        (nb096AlphaDummy078 R q)), ((nb096AlphaDummy073 D R),
        (nb096AlphaDummy075 R q)), ((nb096AlphaDummy074 D R),
        (nb096AlphaDummy076 R q)), ((nb096AlphaDummy099 D R),
        (nb096AlphaDummy100 R q)), ((nb096AlphaDummy097 D R),
        (nb096AlphaDummy098 R q)), ((nb096AlphaDummy066 D R),
        (nb096AlphaDummy068 R q)), ((nb096AlphaDummy065 D R),
        (nb096AlphaDummy067 R q)), ((nb096AlphaDummy095 D R),
        (nb096AlphaDummy096 R q)), ((nb096AlphaDummy069 D R),
        (nb096AlphaDummy070 R q)), ((nb096AlphaDummy052 D R),
        (nb096AlphaDummy054 R q)), ((nb096AlphaDummy051 D R),
        (nb096AlphaDummy053 R q)), ((nb096AlphaDummy049 D R),
        (nb096AlphaDummy050 D R q)), ((nb096AlphaDummy047 D R),
        (nb096AlphaDummy048 D R q)), ((nb096AlphaDummy045 D R),
        (nb096AlphaDummy046 D R q)), ((nb096AlphaDummy042 D R),
        (nb096AlphaDummy044 D R q)), ((nb096AlphaDummy041 D R),
        (nb096AlphaDummy043 D R q)), ((nb096AlphaDummy001 D R),
        (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy080 D
        R) ≠ (nb096AlphaDummy087 D R) from (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0074
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0075
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0072
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0073
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠ (nb096AlphaDummy087 D R) from
        (by
          unfold
            nb096AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0078
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy088 R q) from (by
          unfold
            nb096AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0079
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy085 D R) from (by
          unfold
            nb096AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0076
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy086 R q) from (by
          unfold
            nb096AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0077
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy081 D R), (nb096AlphaDummy084 R q)),
        ((nb096AlphaDummy080 D R), (nb096AlphaDummy083 R q)),
        ((nb096AlphaDummy079 D R), (nb096AlphaDummy082 R q)),
        ((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
        ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
        ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
        ((nb096AlphaDummy099 D R), (nb096AlphaDummy100 R q)),
        ((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)),
        ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
        ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
        ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)),
        ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
        ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy080 D
        R) ≠ (nb096AlphaDummy091 D R) from (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠ (nb096AlphaDummy091 D R) from
        (by
          unfold
            nb096AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0082
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy092 R q) from (by
          unfold
            nb096AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0083
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy080 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0080
                    D R)
                  0)))) (show (nb096AlphaDummy083 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0081
                    R q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy075 R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081 D
        R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy081 D
        R) ≠ (nb096AlphaDummy093 D R) from (by
          unfold
            nb096AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0086
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy094 R q) from (by
          unfold
            nb096AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0087
                    R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy081 D R) ≠
        (nb096AlphaDummy089 D R) from (by
          unfold
            nb096AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0084
                    D R)
                  0)))) (show (nb096AlphaDummy084 R q) ≠ (nb096AlphaDummy090 R q) from (by
          unfold
            nb096AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0085
                    R q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R) from
                                (by
                                  unfold nb096AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0068 D R)
                                          0)))) (show
                                (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from
                                (by
                                  unfold nb096AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0069 R q)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                              ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
                              ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
                              ((nb096AlphaDummy099 D R), (nb096AlphaDummy100 R q)),
                              ((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)),
                              ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
                              ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
                              ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)),
                              ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
                              ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
                              ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
                              ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
                              ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
                              ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
                              ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
                              ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
                              ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                              ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
                                (nb096AlphaDummy004 D R q))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R) from (by
                                unfold nb096AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0068 D R) 0)))) (show
                              (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from (by
                                unfold nb096AlphaDummy078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0069 R q) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb096AlphaDummy073 D R) ≠ (nb096AlphaDummy077 D R) from
                                (by
                                  unfold nb096AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0068 D R)
                                          0)))) (show
                                (nb096AlphaDummy075 R q) ≠ (nb096AlphaDummy078 R q) from
                                (by
                                  unfold nb096AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0069 R q)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb096AlphaDummy077 D R), (nb096AlphaDummy078 R q)),
                              ((nb096AlphaDummy073 D R), (nb096AlphaDummy075 R q)),
                              ((nb096AlphaDummy074 D R), (nb096AlphaDummy076 R q)),
                              ((nb096AlphaDummy099 D R), (nb096AlphaDummy100 R q)),
                              ((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)),
                              ((nb096AlphaDummy066 D R), (nb096AlphaDummy068 R q)),
                              ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R q)),
                              ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)),
                              ((nb096AlphaDummy069 D R), (nb096AlphaDummy070 R q)),
                              ((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
                              ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
                              ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
                              ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
                              ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
                              ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
                              ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
                              ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                              ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
                                (nb096AlphaDummy004 D R q))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb096_focused_notmem_0015 (D : Class) (R : Class) :
    (nb096AlphaDummy052 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcnv (synCdif R (synCid)))).fv ∪
          ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0250 (D : Class) (R : Class) :
    (nb096AlphaDummy052 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy052, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0015 D R) (nb096_compact_fv_empty_0052 D R))

theorem nb096_focused_notmem_0016 (R : Class) (q : Var) :
    (nb096AlphaDummy054 R q) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcnv (synCdif R (synCid)))).fv ∪
          ((synCsn (synCuni (synCuni (Class.cv q))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0251 (R : Class) (q : Var) :
    (nb096AlphaDummy054 R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy054, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0016 R q) (nb096_compact_fv_empty_0053 R q))

theorem nb096_focused_notmem_0017 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcnv (synCdif R (synCid)))).fv ∪
          ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0252 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy051, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0017 D R) (nb096_compact_fv_empty_0054 D R))

theorem nb096_focused_notmem_0018 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ∉ R.fv :=
  by
  change
    freshVar
        (((synCcnv (synCdif R (synCid)))).fv ∪
          ((synCsn (synCuni (synCuni (Class.cv q))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0253 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy053, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0018 R q) (nb096_compact_fv_empty_0055 R q))

theorem nb096_focused_notmem_0019 (D : Class) (R : Class) :
    (nb096AlphaDummy049 D R) ∉ R.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0254 (D : Class) (R : Class) :
    (nb096AlphaDummy049 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy049, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0019 D R) (nb096_compact_fv_empty_0056 D R))

theorem nb096_focused_notmem_0020 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy050 D R q) ∉ R.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0255 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy050 D R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy050, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0020 D R q) (nb096_compact_fv_empty_0057 D R q))

theorem nb096_focused_notmem_0021 (D : Class) (R : Class) :
    (nb096AlphaDummy047 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv ∪
          ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0256 (D : Class) (R : Class) :
    (nb096AlphaDummy047 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy047, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0021 D R) (nb096_compact_fv_empty_0058 D R))

theorem nb096_focused_notmem_0022 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy048 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q))))))).fv ∪ ((synCnin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0257 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy048 D R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy048, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0022 D R q) (nb096_compact_fv_empty_0059 D R q))

theorem nb096_focused_notmem_0023 (D : Class) (R : Class) :
    (nb096AlphaDummy045 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0258 (D : Class) (R : Class) :
    (nb096AlphaDummy045 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy045, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0023 D R) (nb096_compact_fv_empty_0060 D R))

theorem nb096_focused_notmem_0024 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy046 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb096_wpp_notmem_0259 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy046 D R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy046, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0024 D R q) (nb096_compact_fv_empty_0061 D R q))

theorem nb096_focused_notmem_0025 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0260 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy042, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0025 D R) (nb096_compact_fv_empty_0062 D R))

theorem nb096_focused_notmem_0026 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0261 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy044, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0026 D R q) (nb096_compact_fv_empty_0063 D R q))

theorem nb096_focused_notmem_0027 (D : Class) (R : Class) :
    (nb096AlphaDummy041 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0262 (D : Class) (R : Class) :
    (nb096AlphaDummy041 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy041, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0027 D R) (nb096_compact_fv_empty_0064 D R))

theorem nb096_focused_notmem_0028 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy043 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0263 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy043 D R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy043, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0028 D R q) (nb096_compact_fv_empty_0065 D R q))

theorem nb096_focused_notmem_0029 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb096AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0264 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0029 D R) (nb096_compact_fv_empty_0020 D R))

theorem nb096_focused_notmem_0030 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0265 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy002, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0030 D R q) (nb096_compact_fv_empty_0021 D R q))

theorem nb096_focused_notmem_0031 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_wpp_notmem_0266 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy000, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0031 D R) (nb096_compact_fv_empty_0022 D R))

theorem nb096_wpp_notmem_0267 (R : Class) (q : Var) (dv_R_q : q ∉ R.fv) :
    q ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_R_q (nb096_compact_fv_empty_0023 q))

theorem nb096_focused_notmem_0032 (D : Class) (R : Class) :
    (nb096AlphaDummy003 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb096AlphaDummy000 D R)} : Finset Var) ∪
            ({(nb096AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                          (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb096AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb096AlphaDummy001 D R)) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb096AlphaDummy001 D R))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0268 (D : Class) (R : Class) :
    (nb096AlphaDummy003 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy003, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0032 D R) (nb096_compact_fv_empty_0024 D R))

theorem nb096_focused_notmem_0033 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy004 D R q) ∉ R.fv :=
  by
  change
    freshVar
        (({ q } : Finset Var) ∪ ({(nb096AlphaDummy002 D R q)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
              (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv q)))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv q) (synCpw1 (synCpw1 D)))
      (Wff.classEq (Class.cv (nb096AlphaDummy002 D R q)) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb096AlphaDummy002 D R q))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv q)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cnc
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv q))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_wpp_notmem_0269 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy004 D R q) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb096AlphaDummy004, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb096_focused_notmem_0033 D R q) (nb096_compact_fv_empty_0025 D R q))

theorem nb096_compact_envfresh_0016 (D : Class) (R : Class) (q : Var)
    (dv_R_q : q ∉ R.fv) :
    TEnvFresh
      [((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      ((synCcnv (synCdif R (synCid)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096AlphaDummy052 D R) (nb096AlphaDummy054 R q)
      (nb096_wpp_notmem_0250 D R) (nb096_wpp_notmem_0251 R q)
      (TEnvFresh.consFresh (nb096AlphaDummy051 D R) (nb096AlphaDummy053 R q)
        (nb096_wpp_notmem_0252 D R) (nb096_wpp_notmem_0253 R q)
        (TEnvFresh.consFresh (nb096AlphaDummy049 D R) (nb096AlphaDummy050 D R q)
          (nb096_wpp_notmem_0254 D R) (nb096_wpp_notmem_0255 D R q)
          (TEnvFresh.consFresh (nb096AlphaDummy047 D R) (nb096AlphaDummy048 D R q)
            (nb096_wpp_notmem_0256 D R) (nb096_wpp_notmem_0257 D R q)
            (TEnvFresh.consFresh (nb096AlphaDummy045 D R) (nb096AlphaDummy046 D R q)
              (nb096_wpp_notmem_0258 D R) (nb096_wpp_notmem_0259 D R q)
              (TEnvFresh.consFresh (nb096AlphaDummy042 D R)
                (nb096AlphaDummy044 D R q) (nb096_wpp_notmem_0260 D R)
                (nb096_wpp_notmem_0261 D R q) (TEnvFresh.consFresh (nb096AlphaDummy041 D R)
                  (nb096AlphaDummy043 D R q) (nb096_wpp_notmem_0262 D R)
                  (nb096_wpp_notmem_0263 D R q) (TEnvFresh.consFresh (nb096AlphaDummy001 D R)
                    (nb096AlphaDummy002 D R q) (nb096_wpp_notmem_0264 D R)
                    (nb096_wpp_notmem_0265 D R q)
                    (TEnvFresh.consFresh (nb096AlphaDummy000 D R) q
                      (nb096_wpp_notmem_0266 D R) (nb096_wpp_notmem_0267 R q dv_R_q)
                      (TEnvFresh.consFresh (nb096AlphaDummy003 D R)
                        (nb096AlphaDummy004 D R q) (nb096_wpp_notmem_0268 D R)
                        (nb096_wpp_notmem_0269 D R q)
                        (TEnvFresh.nil ((synCcnv (synCdif R (synCid)))).fv)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb096_wpp_refl_0015`. -/
@[expose]
noncomputable def nb096WppRefl0015 (D : Class) (R : Class) (q : Var)
    (dv_R_q : q ∉ R.fv) :
    TReflOn
      [((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      ((synCcnv (synCdif R (synCid)))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0016 D R q dv_R_q)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
