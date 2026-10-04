/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part037`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0023`. -/
@[expose]
noncomputable def nb077SplitAlpha0023 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy137 F I), (nb077AlphaDummy138 x)),
        ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
        ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
        ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
        ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy137 F I))
          (synCphi (Class.cv (nb077AlphaDummy104 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy137 F I))
            (synCphi (Class.cv (nb077AlphaDummy104 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy138 x))
          (synCphi (Class.cv (nb077AlphaDummy106 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy138 x))
            (synCphi (Class.cv (nb077AlphaDummy106 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy111 F I) from (by
                      unfold nb077AlphaDummy111;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0096 F I) 0))))
                  (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy113 x) from (by
                      unfold nb077AlphaDummy113;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0097 x) 0))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy112 F I) from (by
                        unfold nb077AlphaDummy112;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0096 F I) 1))))
                    (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy114 x) from (by
                        unfold nb077AlphaDummy114;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0097 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy137 F I) from (by
                          unfold nb077AlphaDummy137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0126 F I) 0))))
                      (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy138 x) from (by
                          unfold nb077AlphaDummy138;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0127 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy135 F I) from (by
                            unfold nb077AlphaDummy135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0124 F I) 0))))
                        (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy136 x) from (by
                            unfold nb077AlphaDummy136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0125 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077AlphaDummy104 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy106 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy118 F I)
                                      from (by
                                        unfold nb077AlphaDummy118;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0100 F I) 1)))) (show
                                      (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy121 x) from
                                      (by
                                        unfold nb077AlphaDummy121;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0101 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy111 F I) ≠
        (nb077AlphaDummy117 F I) from (by
                                          unfold nb077AlphaDummy117;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0100 F I) 0)))) (show
                                        (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy120 x)
                                        from (by
                                          unfold nb077AlphaDummy120;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0101 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy111 F I) ≠
        (nb077AlphaDummy115 F I) from (by
          unfold nb077AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0098 F I) 0)))) (show (nb077AlphaDummy113 x) ≠
        (nb077AlphaDummy116 x) from (by
          unfold nb077AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0099 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb077AlphaDummy119 F I),
        (nb077AlphaDummy122 x)), ((nb077AlphaDummy118 F I), (nb077AlphaDummy121 x)),
                                        ((nb077AlphaDummy117 F I),
        (nb077AlphaDummy120 x)), ((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)),
                                        ((nb077AlphaDummy111 F I),
        (nb077AlphaDummy113 x)), ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
                                        ((nb077AlphaDummy137 F I),
        (nb077AlphaDummy138 x)), ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
                                        ((nb077AlphaDummy104 F I),
        (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
                                        ((nb077AlphaDummy133 F I),
        (nb077AlphaDummy134 x)), ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
                                        ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                        ((nb077AlphaDummy059 F I),
        (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                        ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy118 F I) ≠ (nb077AlphaDummy125 F I) from (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy125 F I) from (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠ (nb077AlphaDummy125 F I) from
        (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy125 F I) from (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb077AlphaDummy119 F I),
        (nb077AlphaDummy122 x)), ((nb077AlphaDummy118 F I), (nb077AlphaDummy121 x)),
        ((nb077AlphaDummy117 F I), (nb077AlphaDummy120 x)), ((nb077AlphaDummy115 F I),
        (nb077AlphaDummy116 x)), ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
        ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)), ((nb077AlphaDummy137 F I),
        (nb077AlphaDummy138 x)), ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
        ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
        (nb077AlphaDummy105 x)), ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy118 F I) ≠ (nb077AlphaDummy129 F I) from (by
          unfold
            nb077AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy130 x) from (by
          unfold
            nb077AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy129 F I) from (by
          unfold
            nb077AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy130 x) from (by
          unfold
            nb077AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy119 F I) ≠ (nb077AlphaDummy131 F I) from (by
          unfold
            nb077AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy132 x) from (by
          unfold
            nb077AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy119 F I) ≠ (nb077AlphaDummy131 F I) from (by
          unfold
            nb077AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy132 x) from (by
          unfold
            nb077AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I) from (by
                                unfold nb077AlphaDummy115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0098 F I) 0))))
                            (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from (by
                                unfold nb077AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0099 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)),
                            ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
                            ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
                            ((nb077AlphaDummy137 F I), (nb077AlphaDummy138 x)),
                            ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
                            ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
                            ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
                            ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)),
                            ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
                            ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I) from
                            (by
                              unfold nb077AlphaDummy115;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0098 F I) 0))))
                          (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from (by
                              unfold nb077AlphaDummy116;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0099 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I) from (by
                                unfold nb077AlphaDummy115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0098 F I) 0))))
                            (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from (by
                                unfold nb077AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0099 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)),
                            ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
                            ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
                            ((nb077AlphaDummy137 F I), (nb077AlphaDummy138 x)),
                            ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
                            ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
                            ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
                            ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)),
                            ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
                            ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy111 F I) from (by
                        unfold nb077AlphaDummy111;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0096 F I) 0))))
                    (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy113 x) from (by
                        unfold nb077AlphaDummy113;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0097 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy112 F I) from (by
                          unfold nb077AlphaDummy112;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0096 F I) 1))))
                      (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy114 x) from (by
                          unfold nb077AlphaDummy114;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0097 x) 1))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy137 F I) from (by
                            unfold nb077AlphaDummy137;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0126 F I) 0))))
                        (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy138 x) from (by
                            unfold nb077AlphaDummy138;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0127 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy135 F I) from
                            (by
                              unfold nb077AlphaDummy135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0124 F I) 0))))
                          (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy136 x) from (by
                              unfold nb077AlphaDummy136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0125 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077AlphaDummy104 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy106 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077AlphaDummy111 F I) ≠
        (nb077AlphaDummy118 F I) from (by
                                          unfold nb077AlphaDummy118;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0100 F I) 1)))) (show
                                        (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy121 x)
                                        from (by
                                          unfold nb077AlphaDummy121;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0101 x) 1))))
                                      (TAlphaVar.there (show (nb077AlphaDummy111 F I) ≠
        (nb077AlphaDummy117 F I) from (by
          unfold nb077AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I) 0)))) (show (nb077AlphaDummy113 x) ≠
        (nb077AlphaDummy120 x) from (by
          unfold nb077AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I) from (by
          unfold nb077AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0098 F I) 0)))) (show (nb077AlphaDummy113 x) ≠
        (nb077AlphaDummy116 x) from (by
          unfold nb077AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0099 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy119 F I),
        (nb077AlphaDummy122 x)), ((nb077AlphaDummy118 F I), (nb077AlphaDummy121 x)),
        ((nb077AlphaDummy117 F I), (nb077AlphaDummy120 x)), ((nb077AlphaDummy115 F I),
        (nb077AlphaDummy116 x)), ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
        ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)), ((nb077AlphaDummy137 F I),
        (nb077AlphaDummy138 x)), ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
        ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
        (nb077AlphaDummy105 x)), ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy118 F
        I) ≠ (nb077AlphaDummy125 F I) from (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠ (nb077AlphaDummy125 F I) from
        (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠ (nb077AlphaDummy125 F I) from
        (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0104
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0102
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0103
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠ (nb077AlphaDummy125 F I) from
        (by
          unfold
            nb077AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0108
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy126 x) from (by
          unfold
            nb077AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy123 F I) from (by
          unfold
            nb077AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0106
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy124 x) from (by
          unfold
            nb077AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0107
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy119 F I), (nb077AlphaDummy122 x)), ((nb077AlphaDummy118 F I),
        (nb077AlphaDummy121 x)), ((nb077AlphaDummy117 F I), (nb077AlphaDummy120 x)),
        ((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)), ((nb077AlphaDummy111 F I),
        (nb077AlphaDummy113 x)), ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
        ((nb077AlphaDummy137 F I), (nb077AlphaDummy138 x)), ((nb077AlphaDummy135 F I),
        (nb077AlphaDummy136 x)), ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
        ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)), ((nb077AlphaDummy133 F I),
        (nb077AlphaDummy134 x)), ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy118 F
        I) ≠ (nb077AlphaDummy129 F I) from (by
          unfold
            nb077AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy130 x) from (by
          unfold
            nb077AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠ (nb077AlphaDummy129 F I) from
        (by
          unfold
            nb077AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0112
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy130 x) from (by
          unfold
            nb077AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy118 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0110
                    F I)
                  0)))) (show (nb077AlphaDummy121 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0111
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119 F
        I) ≠ (nb077AlphaDummy131 F I) from (by
          unfold
            nb077AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy132 x) from (by
          unfold
            nb077AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119 F
        I) ≠ (nb077AlphaDummy131 F I) from (by
          unfold
            nb077AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0116
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy132 x) from (by
          unfold
            nb077AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0117
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy119 F I) ≠
        (nb077AlphaDummy127 F I) from (by
          unfold
            nb077AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0114
                    F I)
                  0)))) (show (nb077AlphaDummy122 x) ≠ (nb077AlphaDummy128 x) from (by
          unfold
            nb077AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0115
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I) from
                                (by
                                  unfold nb077AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0098 F I)
                                          0))))
                              (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from
                                (by
                                  unfold nb077AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0099 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)),
                              ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
                              ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
                              ((nb077AlphaDummy137 F I), (nb077AlphaDummy138 x)),
                              ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
                              ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
                              ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
                              ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)),
                              ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
                              ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I) from (by
                                unfold nb077AlphaDummy115;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0098 F I) 0))))
                            (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from (by
                                unfold nb077AlphaDummy116;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0099 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I) from
                                (by
                                  unfold nb077AlphaDummy115;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0098 F I)
                                          0))))
                              (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from
                                (by
                                  unfold nb077AlphaDummy116;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0099 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)),
                              ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
                              ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
                              ((nb077AlphaDummy137 F I), (nb077AlphaDummy138 x)),
                              ((nb077AlphaDummy135 F I), (nb077AlphaDummy136 x)),
                              ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
                              ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
                              ((nb077AlphaDummy133 F I), (nb077AlphaDummy134 x)),
                              ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
                              ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part038`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0024`. -/
@[expose]
noncomputable def nb077SplitAlpha0024 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy153 F I), (nb077AlphaDummy154 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy153 F I))
          (Class.cab (nb077AlphaDummy147 F I)
            (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                (synCphi (Class.cv (nb077AlphaDummy148 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy153 F I))
            (Class.cab (nb077AlphaDummy147 F I)
              (synWrex (nb077AlphaDummy148 F I) (Class.cv (nb077AlphaDummy139 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy147 F I))
                  (synCphi (Class.cv (nb077AlphaDummy148 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy154 x))
          (Class.cab (nb077AlphaDummy149 x)
            (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                (synCphi (Class.cv (nb077AlphaDummy150 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy154 x))
            (Class.cab (nb077AlphaDummy149 x)
              (synWrex (nb077AlphaDummy150 x) (Class.cv (nb077AlphaDummy142 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy149 x))
                  (synCphi (Class.cv (nb077AlphaDummy150 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy148 F I) from (by
                      unfold nb077AlphaDummy148;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
                  (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy150 x) from (by
                      unfold nb077AlphaDummy150;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy147 F I) from (by
                        unfold nb077AlphaDummy147;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
                    (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy149 x) from (by
                        unfold nb077AlphaDummy149;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0134 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy153 F I) from (by
                          unfold nb077AlphaDummy153;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0136 F I) 0))))
                      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy154 x) from (by
                          unfold nb077AlphaDummy154;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0137 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy151 F I) from (by
                            unfold nb077AlphaDummy151;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0133 F I) 0))))
                        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy152 x) from (by
                            unfold nb077AlphaDummy152;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0135 x) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                  (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                    (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
                          (freshVar_injective (((synCmpt x (synCvv)
                                  (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy142 x))).fv ∪
                      ((Class.cv (nb077AlphaDummy143 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy155 F I) from
                            (by
                              unfold nb077AlphaDummy155;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                          (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy157 x) from (by
                              unfold nb077AlphaDummy157;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0139 x) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy156 F I) from (by
                                unfold nb077AlphaDummy156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0138 F I) 1))))
                            (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy158 x) from (by
                                unfold nb077AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0139 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy148 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077AlphaDummy150 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy162 F I) from
        (by
          unfold nb077AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I) 1)))) (show (nb077AlphaDummy157 x) ≠
        (nb077AlphaDummy165 x) from (by
          unfold nb077AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy161 F I) from (by
          unfold nb077AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I)
                  0)))) (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy164 x) from (by
          unfold nb077AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from (by
          unfold nb077AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I)
                  0)))) (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from (by
          unfold nb077AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy163 F I), (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I),
        (nb077AlphaDummy165 x)), ((nb077AlphaDummy161 F I), (nb077AlphaDummy164 x)),
        ((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I),
        (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
        ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
        (nb077AlphaDummy149 x)), ((nb077AlphaDummy153 F I), (nb077AlphaDummy154 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy163 F I), (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I),
        (nb077AlphaDummy165 x)), ((nb077AlphaDummy161 F I), (nb077AlphaDummy164 x)),
        ((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I),
        (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
        ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
        (nb077AlphaDummy149 x)), ((nb077AlphaDummy153 F I), (nb077AlphaDummy154 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy157 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy162
        F I) ≠ (nb077AlphaDummy173 F I) from (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy173 F I) from
        (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163
        F I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163
        F I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I)
                                      from (by
                                        unfold nb077AlphaDummy159;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0140 F I) 0)))) (show
                                      (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from
                                      (by
                                        unfold nb077AlphaDummy160;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0141 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy159 F I),
                                      (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I),
                                      (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I),
                                      (nb077AlphaDummy158 x)), ((nb077AlphaDummy148 F I),
                                      (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
                                      (nb077AlphaDummy149 x)), ((nb077AlphaDummy153 F I),
                                      (nb077AlphaDummy154 x)), ((nb077AlphaDummy151 F I),
                                      (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
                                      (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
                                      (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
                                      (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
                                      (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
                                      (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
                                      (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
                                      (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
                                      (nb077AlphaDummy058 x F)),
                                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I)
                                    from (by
                                      unfold nb077AlphaDummy159;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0140 F I)
                                              0)))) (show
                                    (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from
                                    (by
                                      unfold nb077AlphaDummy160;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0141 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I)
                                      from (by
                                        unfold nb077AlphaDummy159;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0140 F I) 0)))) (show
                                      (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from
                                      (by
                                        unfold nb077AlphaDummy160;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0141 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy159 F I),
                                      (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I),
                                      (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I),
                                      (nb077AlphaDummy158 x)), ((nb077AlphaDummy148 F I),
                                      (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
                                      (nb077AlphaDummy149 x)), ((nb077AlphaDummy153 F I),
                                      (nb077AlphaDummy154 x)), ((nb077AlphaDummy151 F I),
                                      (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
                                      (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
                                      (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I),
                                      (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
                                      (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
                                      (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I),
                                      (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
                                      (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
                                      (nb077AlphaDummy058 x F)),
                                    ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                                    ((nb077AlphaDummy016 F I),
                                      (nb077AlphaDummy018 x F I)),
                                    ((nb077AlphaDummy015 F I),
                                      (nb077AlphaDummy017 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy148 F I) from (by
                        unfold nb077AlphaDummy148;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
                    (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy150 x) from (by
                        unfold nb077AlphaDummy150;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0134 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy147 F I) from (by
                          unfold nb077AlphaDummy147;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
                      (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy149 x) from (by
                          unfold nb077AlphaDummy149;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0134 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy153 F I) from (by
                            unfold nb077AlphaDummy153;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0136 F I) 0))))
                        (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy154 x) from (by
                            unfold nb077AlphaDummy154;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0137 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy139 F I) ≠ (nb077AlphaDummy151 F I) from
                            (by
                              unfold nb077AlphaDummy151;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0133 F I) 0))))
                          (show (nb077AlphaDummy142 x) ≠ (nb077AlphaDummy152 x) from (by
                              unfold nb077AlphaDummy152;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0135 x) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                    (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                      (synC1c)))).fv ∪ ((synC1st)).fv) (by decide))
                            (freshVar_injective (((synCmpt x (synCvv)
                                    (synCplc (Class.cv x) (synC1c)))).fv ∪ ((synC1st)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077AlphaDummy139 F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy140 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy142 x))).fv ∪
                        ((Class.cv (nb077AlphaDummy143 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy155 F I) from (by
                                unfold nb077AlphaDummy155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                            (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy157 x) from (by
                                unfold nb077AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0139 x) 0))))
                            (TAlphaVar.there (show
                                (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy156 F I) from
                                (by
                                  unfold nb077AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0138 F I)
                                          1))))
                              (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy158 x) from
                                (by
                                  unfold nb077AlphaDummy158;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0139 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077AlphaDummy148 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077AlphaDummy150 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy162 F I) from (by
          unfold nb077AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I)
                  1)))) (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy165 x) from (by
          unfold nb077AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy161 F I) from (by
          unfold nb077AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I)
                  0)))) (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy164 x) from (by
          unfold nb077AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy155 F I) ≠
        (nb077AlphaDummy159 F I) from (by
          unfold nb077AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I)
                  0)))) (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from (by
          unfold nb077AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy163 F I), (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I),
        (nb077AlphaDummy165 x)), ((nb077AlphaDummy161 F I), (nb077AlphaDummy164 x)),
        ((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I),
        (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
        ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
        (nb077AlphaDummy149 x)), ((nb077AlphaDummy153 F I), (nb077AlphaDummy154 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy163 F I), (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I),
        (nb077AlphaDummy165 x)), ((nb077AlphaDummy161 F I), (nb077AlphaDummy164 x)),
        ((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I),
        (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
        ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
        (nb077AlphaDummy149 x)), ((nb077AlphaDummy153 F I), (nb077AlphaDummy154 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy157
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy162
        F I) ≠ (nb077AlphaDummy173 F I) from (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy173 F I) from
        (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163
        F I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163
        F I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy155 F I) ≠
        (nb077AlphaDummy159 F I) from (by
                                          unfold nb077AlphaDummy159;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0140 F I) 0)))) (show
                                        (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x)
                                        from (by
                                          unfold nb077AlphaDummy160;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0141 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)),
                                      ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
                                      ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
                                      ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
                                      ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
                                      ((nb077AlphaDummy153 F I), (nb077AlphaDummy154 x)),
                                      ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
                                      ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                                      ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                                      ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
                                      ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                      ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                      ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                      ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                      ((nb077AlphaDummy057 F I),
                                        (nb077AlphaDummy058 x F)),
                                      ((nb077AlphaDummy055 F I),
                                        (nb077AlphaDummy056 x F)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I)
                                      from (by
                                        unfold nb077AlphaDummy159;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0140 F I) 0)))) (show
                                      (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from
                                      (by
                                        unfold nb077AlphaDummy160;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0141 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy155 F I) ≠
        (nb077AlphaDummy159 F I) from (by
                                          unfold nb077AlphaDummy159;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0140 F I) 0)))) (show
                                        (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x)
                                        from (by
                                          unfold nb077AlphaDummy160;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0141 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)),
                                      ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
                                      ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
                                      ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
                                      ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
                                      ((nb077AlphaDummy153 F I), (nb077AlphaDummy154 x)),
                                      ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
                                      ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                                      ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                                      ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
                                      ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                      ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                                      ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                      ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                                      ((nb077AlphaDummy057 F I),
                                        (nb077AlphaDummy058 x F)),
                                      ((nb077AlphaDummy055 F I),
                                        (nb077AlphaDummy056 x F)),
                                      ((nb077AlphaDummy016 F I),
                                        (nb077AlphaDummy018 x F I)),
                                      ((nb077AlphaDummy015 F I),
                                        (nb077AlphaDummy017 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part039`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0025`. -/
@[expose]
noncomputable def nb077SplitAlpha0025 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy181 F I), (nb077AlphaDummy182 x)),
        ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
        ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
        ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
        ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
        ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy181 F I))
          (synCphi (Class.cv (nb077AlphaDummy148 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy181 F I))
            (synCphi (Class.cv (nb077AlphaDummy148 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy182 x))
          (synCphi (Class.cv (nb077AlphaDummy150 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy182 x))
            (synCphi (Class.cv (nb077AlphaDummy150 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy155 F I) from (by
                      unfold nb077AlphaDummy155;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                  (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy157 x) from (by
                      unfold nb077AlphaDummy157;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0139 x) 0))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy156 F I) from (by
                        unfold nb077AlphaDummy156;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0138 F I) 1))))
                    (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy158 x) from (by
                        unfold nb077AlphaDummy158;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0139 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy181 F I) from (by
                          unfold nb077AlphaDummy181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0168 F I) 0))))
                      (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy182 x) from (by
                          unfold nb077AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0169 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy179 F I) from (by
                            unfold nb077AlphaDummy179;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0166 F I) 0))))
                        (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy180 x) from (by
                            unfold nb077AlphaDummy180;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0167 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077AlphaDummy148 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy150 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy162 F I)
                                      from (by
                                        unfold nb077AlphaDummy162;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0142 F I) 1)))) (show
                                      (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy165 x) from
                                      (by
                                        unfold nb077AlphaDummy165;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0143 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077AlphaDummy155 F I) ≠
        (nb077AlphaDummy161 F I) from (by
                                          unfold nb077AlphaDummy161;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0142 F I) 0)))) (show
                                        (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy164 x)
                                        from (by
                                          unfold nb077AlphaDummy164;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0143 x) 0))))
                                      (TAlphaVar.there (show (nb077AlphaDummy155 F I) ≠
        (nb077AlphaDummy159 F I) from (by
          unfold nb077AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I) 0)))) (show (nb077AlphaDummy157 x) ≠
        (nb077AlphaDummy160 x) from (by
          unfold nb077AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb077AlphaDummy163 F I),
        (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I), (nb077AlphaDummy165 x)),
                                        ((nb077AlphaDummy161 F I),
        (nb077AlphaDummy164 x)), ((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)),
                                        ((nb077AlphaDummy155 F I),
        (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
                                        ((nb077AlphaDummy181 F I),
        (nb077AlphaDummy182 x)), ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
                                        ((nb077AlphaDummy148 F I),
        (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
                                        ((nb077AlphaDummy177 F I),
        (nb077AlphaDummy178 x)), ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
                                        ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                                        ((nb077AlphaDummy145 F I),
        (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                                        ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                                        ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                                        ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy169 F I) from (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy169 F I) from (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy169 F I) from (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb077AlphaDummy163 F I),
        (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I), (nb077AlphaDummy165 x)),
        ((nb077AlphaDummy161 F I), (nb077AlphaDummy164 x)), ((nb077AlphaDummy159 F I),
        (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
        ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)), ((nb077AlphaDummy181 F I),
        (nb077AlphaDummy182 x)), ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
        ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
        (nb077AlphaDummy149 x)), ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy173 F I) from (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy173 F I) from (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from (by
                                unfold nb077AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                            (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from (by
                                unfold nb077AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)),
                            ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
                            ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
                            ((nb077AlphaDummy181 F I), (nb077AlphaDummy182 x)),
                            ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
                            ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
                            ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
                            ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)),
                            ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
                            ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                            ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                            ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
                            ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from
                            (by
                              unfold nb077AlphaDummy159;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                          (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from (by
                              unfold nb077AlphaDummy160;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from (by
                                unfold nb077AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                            (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from (by
                                unfold nb077AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)),
                            ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
                            ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
                            ((nb077AlphaDummy181 F I), (nb077AlphaDummy182 x)),
                            ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
                            ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
                            ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
                            ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)),
                            ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
                            ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                            ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                            ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
                            ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                            ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                            ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                            ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                            ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                            ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                            ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                            ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                            ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                            ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                            ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy155 F I) from (by
                        unfold nb077AlphaDummy155;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                    (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy157 x) from (by
                        unfold nb077AlphaDummy157;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0139 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy156 F I) from (by
                          unfold nb077AlphaDummy156;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0138 F I) 1))))
                      (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy158 x) from (by
                          unfold nb077AlphaDummy158;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0139 x) 1))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy181 F I) from (by
                            unfold nb077AlphaDummy181;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0168 F I) 0))))
                        (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy182 x) from (by
                            unfold nb077AlphaDummy182;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0169 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy148 F I) ≠ (nb077AlphaDummy179 F I) from
                            (by
                              unfold nb077AlphaDummy179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0166 F I) 0))))
                          (show (nb077AlphaDummy150 x) ≠ (nb077AlphaDummy180 x) from (by
                              unfold nb077AlphaDummy180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0167 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077AlphaDummy148 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy150 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077AlphaDummy155 F I) ≠
        (nb077AlphaDummy162 F I) from (by
                                          unfold nb077AlphaDummy162;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0142 F I) 1)))) (show
                                        (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy165 x)
                                        from (by
                                          unfold nb077AlphaDummy165;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0143 x) 1))))
                                      (TAlphaVar.there (show (nb077AlphaDummy155 F I) ≠
        (nb077AlphaDummy161 F I) from (by
          unfold nb077AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I) 0)))) (show (nb077AlphaDummy157 x) ≠
        (nb077AlphaDummy164 x) from (by
          unfold nb077AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 0)))) (TAlphaVar.there (show
        (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from (by
          unfold nb077AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I) 0)))) (show (nb077AlphaDummy157 x) ≠
        (nb077AlphaDummy160 x) from (by
          unfold nb077AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb077AlphaDummy163 F I),
        (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I), (nb077AlphaDummy165 x)),
        ((nb077AlphaDummy161 F I), (nb077AlphaDummy164 x)), ((nb077AlphaDummy159 F I),
        (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
        ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)), ((nb077AlphaDummy181 F I),
        (nb077AlphaDummy182 x)), ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
        ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)), ((nb077AlphaDummy147 F I),
        (nb077AlphaDummy149 x)), ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)),
        ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)), ((nb077AlphaDummy140 F I),
        (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
        ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy162 F
        I) ≠ (nb077AlphaDummy169 F I) from (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠ (nb077AlphaDummy169 F I) from
        (by
          unfold
            nb077AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy170 x) from (by
          unfold
            nb077AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy167 F I) from (by
          unfold
            nb077AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy168 x) from (by
          unfold
            nb077AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy163 F I), (nb077AlphaDummy166 x)), ((nb077AlphaDummy162 F I),
        (nb077AlphaDummy165 x)), ((nb077AlphaDummy161 F I), (nb077AlphaDummy164 x)),
        ((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)), ((nb077AlphaDummy155 F I),
        (nb077AlphaDummy157 x)), ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
        ((nb077AlphaDummy181 F I), (nb077AlphaDummy182 x)), ((nb077AlphaDummy179 F I),
        (nb077AlphaDummy180 x)), ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
        ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)), ((nb077AlphaDummy177 F I),
        (nb077AlphaDummy178 x)), ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
        ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)), ((nb077AlphaDummy139 F I),
        (nb077AlphaDummy142 x)), ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I),
        (nb077AlphaDummy063 x)), ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I),
        (nb077AlphaDummy058 x F)), ((nb077AlphaDummy055 F I),
        (nb077AlphaDummy056 x F)), ((nb077AlphaDummy016 F I),
        (nb077AlphaDummy018 x F I)), ((nb077AlphaDummy015 F I),
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy001 F I),
        (nb077AlphaDummy002 x F I)), ((nb077AlphaDummy004 F I),
        (nb077AlphaDummy006 x F I)), ((nb077AlphaDummy003 F I),
        (nb077AlphaDummy005 x F I))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy155 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy162 F
        I) ≠ (nb077AlphaDummy173 F I) from (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠ (nb077AlphaDummy173 F I) from
        (by
          unfold
            nb077AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy174 x) from (by
          unfold
            nb077AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy162 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077AlphaDummy165 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy155
        F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy157 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163 F
        I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy163 F
        I) ≠ (nb077AlphaDummy175 F I) from (by
          unfold
            nb077AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy176 x) from (by
          unfold
            nb077AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy163 F I) ≠
        (nb077AlphaDummy171 F I) from (by
          unfold
            nb077AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077AlphaDummy166 x) ≠ (nb077AlphaDummy172 x) from (by
          unfold
            nb077AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from
                                (by
                                  unfold nb077AlphaDummy159;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0140 F I)
                                          0))))
                              (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from
                                (by
                                  unfold nb077AlphaDummy160;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)),
                              ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
                              ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
                              ((nb077AlphaDummy181 F I), (nb077AlphaDummy182 x)),
                              ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
                              ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
                              ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
                              ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)),
                              ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
                              ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                              ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                              ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
                              ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from (by
                                unfold nb077AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                            (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from (by
                                unfold nb077AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077AlphaDummy155 F I) ≠ (nb077AlphaDummy159 F I) from
                                (by
                                  unfold nb077AlphaDummy159;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0140 F I)
                                          0))))
                              (show (nb077AlphaDummy157 x) ≠ (nb077AlphaDummy160 x) from
                                (by
                                  unfold nb077AlphaDummy160;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb077AlphaDummy159 F I), (nb077AlphaDummy160 x)),
                              ((nb077AlphaDummy155 F I), (nb077AlphaDummy157 x)),
                              ((nb077AlphaDummy156 F I), (nb077AlphaDummy158 x)),
                              ((nb077AlphaDummy181 F I), (nb077AlphaDummy182 x)),
                              ((nb077AlphaDummy179 F I), (nb077AlphaDummy180 x)),
                              ((nb077AlphaDummy148 F I), (nb077AlphaDummy150 x)),
                              ((nb077AlphaDummy147 F I), (nb077AlphaDummy149 x)),
                              ((nb077AlphaDummy177 F I), (nb077AlphaDummy178 x)),
                              ((nb077AlphaDummy151 F I), (nb077AlphaDummy152 x)),
                              ((nb077AlphaDummy140 F I), (nb077AlphaDummy143 x)),
                              ((nb077AlphaDummy139 F I), (nb077AlphaDummy142 x)),
                              ((nb077AlphaDummy145 F I), (nb077AlphaDummy146 x)),
                              ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
                              ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
                              ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
                              ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
                              ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
                              ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
                              ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
                              ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
