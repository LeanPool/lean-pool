/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part016

/-! NF weak partition development: NAR4H5C095M3Part017. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0023`. -/
@[expose]
noncomputable def nb095SplitAlpha0023 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
          (Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
            (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
          (Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
            (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCphi (Class.cv (nb095AlphaDummy100 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                      (nb095AlphaDummy098 D R S_cls E) from (by
                      unfold nb095AlphaDummy098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                  (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                      unfold nb095AlphaDummy100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy097 D R S_cls E) from (by
                        unfold nb095AlphaDummy097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                        unfold nb095AlphaDummy099;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy103 D R S_cls E) from (by
                          unfold nb095AlphaDummy103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                          unfold nb095AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy101 D R S_cls E) from (by
                            unfold nb095AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                            unfold nb095AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                              (nb095AlphaDummy105 D R S_cls E) from (by
                              unfold nb095AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                              unfold nb095AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy106 D R S_cls E) from (by
                                unfold nb095AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                                unfold nb095AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy105 D R S_cls E) ≠
                                      (nb095AlphaDummy109 D R S_cls E) from (by
                                      unfold nb095AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                    (by
                                      unfold nb095AlphaDummy110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy098 D R S_cls E) from (by
                        unfold nb095AlphaDummy098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                        unfold nb095AlphaDummy100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy097 D R S_cls E) from (by
                          unfold nb095AlphaDummy097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                          unfold nb095AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy103 D R S_cls E) from (by
                            unfold nb095AlphaDummy103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                            unfold nb095AlphaDummy104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                              (nb095AlphaDummy101 D R S_cls E) from (by
                              unfold nb095AlphaDummy101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                              unfold nb095AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                            (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy105 D R S_cls E) from (by
                                unfold nb095AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 0))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                                unfold nb095AlphaDummy107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                  (nb095AlphaDummy106 D R S_cls E) from (by
                                  unfold nb095AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0090 D R S_cls E) 1))))
                              (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from
                                (by
                                  unfold nb095AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy100 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy206 D R S_cls E),
                                        (nb095AlphaDummy208 f)),
                                      ((nb095AlphaDummy205 D R S_cls E),
                                        (nb095AlphaDummy207 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy206 D R S_cls E),
                                        (nb095AlphaDummy208 f)),
                                      ((nb095AlphaDummy205 D R S_cls E),
                                        (nb095AlphaDummy207 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0024`. -/
@[expose]
noncomputable def nb095SplitAlpha0024 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy129 D R S_cls E))
          (synCcompl (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy129 D R S_cls E))
            (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy130 f))
          (synCcompl (synCphi (Class.cv (nb095AlphaDummy100 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy130 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                              (nb095AlphaDummy105 D R S_cls E) from (by
                              unfold nb095AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                              unfold nb095AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy106 D R S_cls E) from (by
                                unfold nb095AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                                unfold nb095AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                  (nb095AlphaDummy131 D R S_cls E) from (by
                                  unfold nb095AlphaDummy131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0120 D R S_cls E) 0))))
                              (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy132 f) from
                                (by
                                  unfold nb095AlphaDummy132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                    (nb095AlphaDummy129 D R S_cls E) from (by
                                    unfold nb095AlphaDummy129;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0118 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy130 f) from (by
                                    unfold nb095AlphaDummy130;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0119 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
        ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
        ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy131 D R S_cls E),
                                      (nb095AlphaDummy132 f)),
                                    ((nb095AlphaDummy129 D R S_cls E),
                                      (nb095AlphaDummy130 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy127 D R S_cls E),
                                      (nb095AlphaDummy128 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy105 D R S_cls E) ≠
                                      (nb095AlphaDummy109 D R S_cls E) from (by
                                      unfold nb095AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                    (by
                                      unfold nb095AlphaDummy110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy131 D R S_cls E),
                                      (nb095AlphaDummy132 f)),
                                    ((nb095AlphaDummy129 D R S_cls E),
                                      (nb095AlphaDummy130 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy127 D R S_cls E),
                                      (nb095AlphaDummy128 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                              (nb095AlphaDummy105 D R S_cls E) from (by
                              unfold nb095AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                              unfold nb095AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy106 D R S_cls E) from (by
                                unfold nb095AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                                unfold nb095AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                  (nb095AlphaDummy131 D R S_cls E) from (by
                                  unfold nb095AlphaDummy131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0120 D R S_cls E) 0))))
                              (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy132 f) from
                                (by
                                  unfold nb095AlphaDummy132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                    (nb095AlphaDummy129 D R S_cls E) from (by
                                    unfold nb095AlphaDummy129;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0118 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy130 f) from (by
                                    unfold nb095AlphaDummy130;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0119 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
        ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy131 D R S_cls E), (nb095AlphaDummy132 f)),
        ((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy131 D R S_cls E),
                                      (nb095AlphaDummy132 f)),
                                    ((nb095AlphaDummy129 D R S_cls E),
                                      (nb095AlphaDummy130 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy127 D R S_cls E),
                                      (nb095AlphaDummy128 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy105 D R S_cls E) ≠
                                      (nb095AlphaDummy109 D R S_cls E) from (by
                                      unfold nb095AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                    (by
                                      unfold nb095AlphaDummy110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy131 D R S_cls E),
                                      (nb095AlphaDummy132 f)),
                                    ((nb095AlphaDummy129 D R S_cls E),
                                      (nb095AlphaDummy130 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy127 D R S_cls E),
                                      (nb095AlphaDummy128 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed
          [((nb095AlphaDummy129 D R S_cls E), (nb095AlphaDummy130 f)),
            ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
            ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
            ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
            ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
            ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
            ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
            ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
            ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
            ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
            ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
            ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0025`. -/
@[expose]
noncomputable def nb095SplitAlpha0025 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy139 D R S_cls E), (nb095AlphaDummy140 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy139 D R S_cls E))
          (Class.cab (nb095AlphaDummy133 D R S_cls E)
            (synWrex (nb095AlphaDummy134 D R S_cls E)
              (Class.cv (nb095AlphaDummy092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy139 D R S_cls E))
            (Class.cab (nb095AlphaDummy133 D R S_cls E)
              (synWrex (nb095AlphaDummy134 D R S_cls E)
                (Class.cv (nb095AlphaDummy092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy133 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy140 f))
          (Class.cab (nb095AlphaDummy135 f)
            (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                (synCphi (Class.cv (nb095AlphaDummy136 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy140 f))
            (Class.cab (nb095AlphaDummy135 f)
              (synWrex (nb095AlphaDummy136 f) (Class.cv (nb095AlphaDummy094 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy135 f))
                  (synCphi (Class.cv (nb095AlphaDummy136 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
                      (nb095AlphaDummy134 D R S_cls E) from (by
                      unfold nb095AlphaDummy134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 1))))
                  (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy136 f) from (by
                      unfold nb095AlphaDummy136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0124 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
                        (nb095AlphaDummy133 D R S_cls E) from (by
                        unfold nb095AlphaDummy133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 0))))
                    (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy135 f) from (by
                        unfold nb095AlphaDummy135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0124 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy092 D R S_cls E) ≠
                          (nb095AlphaDummy139 D R S_cls E) from (by
                          unfold nb095AlphaDummy139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0126 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy140 f) from (by
                          unfold nb095AlphaDummy140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0127 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
                            (nb095AlphaDummy137 D R S_cls E) from (by
                            unfold nb095AlphaDummy137;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0123 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy138 f) from (by
                            unfold nb095AlphaDummy138;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0125 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                              (nb095AlphaDummy141 D R S_cls E) from (by
                              unfold nb095AlphaDummy141;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy143 f) from (by
                              unfold nb095AlphaDummy143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0129 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                                (nb095AlphaDummy142 D R S_cls E) from (by
                                unfold nb095AlphaDummy142;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0128 D R S_cls E) 1))))
                            (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy144 f) from (by
                                unfold nb095AlphaDummy144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0129 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy136 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy141 D R S_cls E) ≠
        (nb095AlphaDummy148 D R S_cls E) from (by
          unfold nb095AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy151 f) from (by
          unfold nb095AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy141 D R S_cls E) ≠ (nb095AlphaDummy147 D R S_cls E) from (by
          unfold nb095AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy150 f) from (by
          unfold nb095AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy141 D R S_cls E) ≠ (nb095AlphaDummy145 D R S_cls E) from (by
          unfold nb095AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0130 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
          unfold nb095AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy149 D R S_cls E), (nb095AlphaDummy152 f)),
        ((nb095AlphaDummy148 D R S_cls E), (nb095AlphaDummy151 f)),
        ((nb095AlphaDummy147 D R S_cls E), (nb095AlphaDummy150 f)),
        ((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
        ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
        ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy139 D R S_cls E), (nb095AlphaDummy140 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy148
        D R S_cls E) ≠ (nb095AlphaDummy155 D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy155
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy155
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy155
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy149 D R S_cls E), (nb095AlphaDummy152 f)),
        ((nb095AlphaDummy148 D R S_cls E), (nb095AlphaDummy151 f)),
        ((nb095AlphaDummy147 D R S_cls E), (nb095AlphaDummy150 f)),
        ((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
        ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
        ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy139 D R S_cls E), (nb095AlphaDummy140 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy159
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy160 f) from (by
          unfold
            nb095AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy159
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy160 f) from (by
          unfold
            nb095AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy149
        D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy162 f) from (by
          unfold
            nb095AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy149
        D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy162 f) from (by
          unfold
            nb095AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy141 D R S_cls E) ≠
                                        (nb095AlphaDummy145 D R S_cls E) from (by
                                        unfold nb095AlphaDummy145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from
                                      (by
                                        unfold nb095AlphaDummy146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy145 D R S_cls E),
                                      (nb095AlphaDummy146 f)),
                                    ((nb095AlphaDummy141 D R S_cls E),
                                      (nb095AlphaDummy143 f)),
                                    ((nb095AlphaDummy142 D R S_cls E),
                                      (nb095AlphaDummy144 f)),
                                    ((nb095AlphaDummy134 D R S_cls E),
                                      (nb095AlphaDummy136 f)),
                                    ((nb095AlphaDummy133 D R S_cls E),
                                      (nb095AlphaDummy135 f)),
                                    ((nb095AlphaDummy139 D R S_cls E),
                                      (nb095AlphaDummy140 f)),
                                    ((nb095AlphaDummy137 D R S_cls E),
                                      (nb095AlphaDummy138 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy141 D R S_cls E) ≠
                                      (nb095AlphaDummy145 D R S_cls E) from (by
                                      unfold nb095AlphaDummy145;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from
                                    (by
                                      unfold nb095AlphaDummy146;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0131 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy141 D R S_cls E) ≠
                                        (nb095AlphaDummy145 D R S_cls E) from (by
                                        unfold nb095AlphaDummy145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from
                                      (by
                                        unfold nb095AlphaDummy146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy145 D R S_cls E),
                                      (nb095AlphaDummy146 f)),
                                    ((nb095AlphaDummy141 D R S_cls E),
                                      (nb095AlphaDummy143 f)),
                                    ((nb095AlphaDummy142 D R S_cls E),
                                      (nb095AlphaDummy144 f)),
                                    ((nb095AlphaDummy134 D R S_cls E),
                                      (nb095AlphaDummy136 f)),
                                    ((nb095AlphaDummy133 D R S_cls E),
                                      (nb095AlphaDummy135 f)),
                                    ((nb095AlphaDummy139 D R S_cls E),
                                      (nb095AlphaDummy140 f)),
                                    ((nb095AlphaDummy137 D R S_cls E),
                                      (nb095AlphaDummy138 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy206 D R S_cls E),
                                      (nb095AlphaDummy208 f)),
                                    ((nb095AlphaDummy205 D R S_cls E),
                                      (nb095AlphaDummy207 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
                        (nb095AlphaDummy134 D R S_cls E) from (by
                        unfold nb095AlphaDummy134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 1))))
                    (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy136 f) from (by
                        unfold nb095AlphaDummy136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0124 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy092 D R S_cls E) ≠
                          (nb095AlphaDummy133 D R S_cls E) from (by
                          unfold nb095AlphaDummy133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy135 f) from (by
                          unfold nb095AlphaDummy135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0124 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
                            (nb095AlphaDummy139 D R S_cls E) from (by
                            unfold nb095AlphaDummy139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0126 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy140 f) from (by
                            unfold nb095AlphaDummy140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0127 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
                              (nb095AlphaDummy137 D R S_cls E) from (by
                              unfold nb095AlphaDummy137;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0123 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy138 f) from (by
                              unfold nb095AlphaDummy138;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0125 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy134 D R S_cls E) ≠
                                (nb095AlphaDummy141 D R S_cls E) from (by
                                unfold nb095AlphaDummy141;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0128 D R S_cls E) 0))))
                            (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy143 f) from (by
                                unfold nb095AlphaDummy143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0129 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                                  (nb095AlphaDummy142 D R S_cls E) from (by
                                  unfold nb095AlphaDummy142;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0128 D R S_cls E) 1))))
                              (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy144 f) from
                                (by
                                  unfold nb095AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0129 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy136 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy141 D R S_cls E) ≠ (nb095AlphaDummy148 D R S_cls E) from (by
          unfold nb095AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy151 f) from (by
          unfold nb095AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy141 D R S_cls E) ≠ (nb095AlphaDummy147 D R S_cls E) from (by
          unfold nb095AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy150 f) from (by
          unfold nb095AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy141 D R S_cls E) ≠
        (nb095AlphaDummy145 D R S_cls E) from (by
          unfold nb095AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0130 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
          unfold nb095AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy149 D R S_cls E), (nb095AlphaDummy152 f)),
        ((nb095AlphaDummy148 D R S_cls E), (nb095AlphaDummy151 f)),
        ((nb095AlphaDummy147 D R S_cls E), (nb095AlphaDummy150 f)),
        ((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
        ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
        ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy139 D R S_cls E), (nb095AlphaDummy140 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy148
        D R S_cls E) ≠ (nb095AlphaDummy155 D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy155
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy155
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy155
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy156 f) from (by
          unfold
            nb095AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy153 D R S_cls E) from (by
          unfold
            nb095AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy149 D R S_cls E), (nb095AlphaDummy152 f)),
        ((nb095AlphaDummy148 D R S_cls E), (nb095AlphaDummy151 f)),
        ((nb095AlphaDummy147 D R S_cls E), (nb095AlphaDummy150 f)),
        ((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
        ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
        ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy139 D R S_cls E), (nb095AlphaDummy140 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
        ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy159
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy160 f) from (by
          unfold
            nb095AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy159
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy160 f) from (by
          unfold
            nb095AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy149
        D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy162 f) from (by
          unfold
            nb095AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy149
        D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy162 f) from (by
          unfold
            nb095AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy157 D R S_cls E) from (by
          unfold
            nb095AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy158 f) from (by
          unfold
            nb095AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy141 D R S_cls E) ≠
        (nb095AlphaDummy145 D R S_cls E) from (by
                                          unfold nb095AlphaDummy145;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0130 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy143 f) ≠
        (nb095AlphaDummy146 f) from (by
                                          unfold nb095AlphaDummy146;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy145 D R S_cls E),
                                        (nb095AlphaDummy146 f)),
                                      ((nb095AlphaDummy141 D R S_cls E),
                                        (nb095AlphaDummy143 f)),
                                      ((nb095AlphaDummy142 D R S_cls E),
                                        (nb095AlphaDummy144 f)),
                                      ((nb095AlphaDummy134 D R S_cls E),
                                        (nb095AlphaDummy136 f)),
                                      ((nb095AlphaDummy133 D R S_cls E),
                                        (nb095AlphaDummy135 f)),
                                      ((nb095AlphaDummy139 D R S_cls E),
                                        (nb095AlphaDummy140 f)),
                                      ((nb095AlphaDummy137 D R S_cls E),
                                        (nb095AlphaDummy138 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy206 D R S_cls E),
                                        (nb095AlphaDummy208 f)),
                                      ((nb095AlphaDummy205 D R S_cls E),
                                        (nb095AlphaDummy207 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy141 D R S_cls E) ≠
                                        (nb095AlphaDummy145 D R S_cls E) from (by
                                        unfold nb095AlphaDummy145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from
                                      (by
                                        unfold nb095AlphaDummy146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy141 D R S_cls E) ≠
        (nb095AlphaDummy145 D R S_cls E) from (by
                                          unfold nb095AlphaDummy145;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0130 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy143 f) ≠
        (nb095AlphaDummy146 f) from (by
                                          unfold nb095AlphaDummy146;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy145 D R S_cls E),
                                        (nb095AlphaDummy146 f)),
                                      ((nb095AlphaDummy141 D R S_cls E),
                                        (nb095AlphaDummy143 f)),
                                      ((nb095AlphaDummy142 D R S_cls E),
                                        (nb095AlphaDummy144 f)),
                                      ((nb095AlphaDummy134 D R S_cls E),
                                        (nb095AlphaDummy136 f)),
                                      ((nb095AlphaDummy133 D R S_cls E),
                                        (nb095AlphaDummy135 f)),
                                      ((nb095AlphaDummy139 D R S_cls E),
                                        (nb095AlphaDummy140 f)),
                                      ((nb095AlphaDummy137 D R S_cls E),
                                        (nb095AlphaDummy138 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy206 D R S_cls E),
                                        (nb095AlphaDummy208 f)),
                                      ((nb095AlphaDummy205 D R S_cls E),
                                        (nb095AlphaDummy207 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
