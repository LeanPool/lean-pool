/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part028`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0004`. -/
@[expose]
noncomputable def nb090SplitAlpha0004 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)),
        ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)),
        ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
        ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
        ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)),
        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy127 A))
          (synCphi (Class.cv (nb090AlphaDummy094 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy127 A))
            (synCphi (Class.cv (nb090AlphaDummy094 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy128 h))
          (synCphi (Class.cv (nb090AlphaDummy096 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy128 h))
            (synCphi (Class.cv (nb090AlphaDummy096 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy101 A) from (by
                      unfold nb090AlphaDummy101;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                  (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy103 h) from (by
                      unfold nb090AlphaDummy103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0091 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy102 A) from (by
                        unfold nb090AlphaDummy102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                    (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy104 h) from (by
                        unfold nb090AlphaDummy104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0091 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy127 A) from (by
                          unfold nb090AlphaDummy127;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0120 A) 0))))
                      (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy128 h) from (by
                          unfold nb090AlphaDummy128;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0121 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy125 A) from (by
                            unfold nb090AlphaDummy125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0118 A) 0))))
                        (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy126 h) from (by
                            unfold nb090AlphaDummy126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0119 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy094 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy096 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy108 A) from
                                      (by
                                        unfold nb090AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0094 A)
                                                1)))) (show (nb090AlphaDummy103 h) ≠
                                        (nb090AlphaDummy111 h) from (by
                                        unfold nb090AlphaDummy111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0095 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy107 A)
                                        from (by
                                          unfold nb090AlphaDummy107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0094 A) 0)))) (show
                                        (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy110 h)
                                        from (by
                                          unfold nb090AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0095 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy101 A) ≠
        (nb090AlphaDummy105 A) from (by
          unfold nb090AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A) 0)))) (show (nb090AlphaDummy103 h) ≠
        (nb090AlphaDummy106 h) from (by
          unfold nb090AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy109 A),
        (nb090AlphaDummy112 h)), ((nb090AlphaDummy108 A), (nb090AlphaDummy111 h)),
                                        ((nb090AlphaDummy107 A), (nb090AlphaDummy110 h)),
                                        ((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                                        ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                                        ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                                        ((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)),
                                        ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)),
                                        ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                                        ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                                        ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)),
                                        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                                        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                        ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy109 A), (nb090AlphaDummy112 h)),
        ((nb090AlphaDummy108 A), (nb090AlphaDummy111 h)), ((nb090AlphaDummy107 A),
        (nb090AlphaDummy110 h)), ((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
        ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)), ((nb090AlphaDummy102 A),
        (nb090AlphaDummy104 h)), ((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)),
        ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)), ((nb090AlphaDummy094 A),
        (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
        ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)), ((nb090AlphaDummy097 A),
        (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from (by
                                unfold nb090AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                            (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from (by
                                unfold nb090AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                            ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                            ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                            ((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)),
                            ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)),
                            ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                            ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                            ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)),
                            ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                            ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                            ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                            ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                            ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                            ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                            ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from (by
                              unfold nb090AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                          (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from (by
                              unfold nb090AlphaDummy106;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from (by
                                unfold nb090AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                            (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from (by
                                unfold nb090AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                            ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                            ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                            ((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)),
                            ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)),
                            ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                            ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                            ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)),
                            ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                            ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                            ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                            ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                            ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                            ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                            ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy101 A) from (by
                        unfold nb090AlphaDummy101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                    (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy103 h) from (by
                        unfold nb090AlphaDummy103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0091 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy102 A) from (by
                          unfold nb090AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                      (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy104 h) from (by
                          unfold nb090AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0091 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy127 A) from (by
                            unfold nb090AlphaDummy127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0120 A) 0))))
                        (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy128 h) from (by
                            unfold nb090AlphaDummy128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0121 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy094 A) ≠ (nb090AlphaDummy125 A) from (by
                              unfold nb090AlphaDummy125;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0118 A) 0))))
                          (show (nb090AlphaDummy096 h) ≠ (nb090AlphaDummy126 h) from (by
                              unfold nb090AlphaDummy126;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0119 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy094 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy096 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy101 A) ≠
        (nb090AlphaDummy108 A) from (by
                                          unfold nb090AlphaDummy108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0094 A) 1)))) (show
                                        (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy111 h)
                                        from (by
                                          unfold nb090AlphaDummy111;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0095 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy101 A) ≠
        (nb090AlphaDummy107 A) from (by
          unfold nb090AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 0)))) (show (nb090AlphaDummy103 h) ≠
        (nb090AlphaDummy110 h) from (by
          unfold nb090AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from (by
          unfold nb090AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A) 0)))) (show (nb090AlphaDummy103 h) ≠
        (nb090AlphaDummy106 h) from (by
          unfold nb090AlphaDummy106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy109 A),
        (nb090AlphaDummy112 h)), ((nb090AlphaDummy108 A), (nb090AlphaDummy111 h)),
        ((nb090AlphaDummy107 A), (nb090AlphaDummy110 h)), ((nb090AlphaDummy105 A),
        (nb090AlphaDummy106 h)), ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
        ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)), ((nb090AlphaDummy127 A),
        (nb090AlphaDummy128 h)), ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)),
        ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)), ((nb090AlphaDummy093 A),
        (nb090AlphaDummy095 h)), ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)),
        ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy115 A) from (by
          unfold
            nb090AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy116 h) from (by
          unfold
            nb090AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy113 A) from (by
          unfold
            nb090AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy114 h) from (by
          unfold
            nb090AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy109 A), (nb090AlphaDummy112 h)), ((nb090AlphaDummy108 A),
        (nb090AlphaDummy111 h)), ((nb090AlphaDummy107 A), (nb090AlphaDummy110 h)),
        ((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)), ((nb090AlphaDummy101 A),
        (nb090AlphaDummy103 h)), ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
        ((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)), ((nb090AlphaDummy125 A),
        (nb090AlphaDummy126 h)), ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
        ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)), ((nb090AlphaDummy123 A),
        (nb090AlphaDummy124 h)), ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy103 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy119 A) from (by
          unfold
            nb090AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy120 h) from (by
          unfold
            nb090AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy108 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy101
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy109 A) ≠ (nb090AlphaDummy121 A) from (by
          unfold
            nb090AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy122 h) from (by
          unfold
            nb090AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy109 A) ≠
        (nb090AlphaDummy117 A) from (by
          unfold
            nb090AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090AlphaDummy112 h) ≠ (nb090AlphaDummy118 h) from (by
          unfold
            nb090AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from
                                (by
                                  unfold nb090AlphaDummy105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                              (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from
                                (by
                                  unfold nb090AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                              ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                              ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                              ((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)),
                              ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)),
                              ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                              ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                              ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)),
                              ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                              ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                              ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                              ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                              ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                              ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                              ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from (by
                                unfold nb090AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                            (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from (by
                                unfold nb090AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy105 A) from
                                (by
                                  unfold nb090AlphaDummy105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                              (show (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy106 h) from
                                (by
                                  unfold nb090AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy105 A), (nb090AlphaDummy106 h)),
                              ((nb090AlphaDummy101 A), (nb090AlphaDummy103 h)),
                              ((nb090AlphaDummy102 A), (nb090AlphaDummy104 h)),
                              ((nb090AlphaDummy127 A), (nb090AlphaDummy128 h)),
                              ((nb090AlphaDummy125 A), (nb090AlphaDummy126 h)),
                              ((nb090AlphaDummy094 A), (nb090AlphaDummy096 h)),
                              ((nb090AlphaDummy093 A), (nb090AlphaDummy095 h)),
                              ((nb090AlphaDummy123 A), (nb090AlphaDummy124 h)),
                              ((nb090AlphaDummy097 A), (nb090AlphaDummy098 h)),
                              ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                              ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                              ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                              ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                              ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                              ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part029`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0005`. -/
@[expose]
noncomputable def nb090SplitAlpha0005 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy141 A))
          (Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy141 A))
            (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCphi (Class.cv (nb090AlphaDummy136 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy142 h))
          (Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy142 h))
            (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCphi (Class.cv (nb090AlphaDummy138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
                      unfold nb090AlphaDummy136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                  (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
                      unfold nb090AlphaDummy138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
                        unfold nb090AlphaDummy135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                    (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
                        unfold nb090AlphaDummy137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy141 A) from (by
                          unfold nb090AlphaDummy141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy142 h) from (by
                          unfold nb090AlphaDummy142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy139 A) from (by
                            unfold nb090AlphaDummy139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy140 h) from (by
                            unfold nb090AlphaDummy140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy129 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy131 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                              unfold nb090AlphaDummy143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                          (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                              unfold nb090AlphaDummy145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                                unfold nb090AlphaDummy144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                                unfold nb090AlphaDummy146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                    ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                    ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                    ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                    ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                    ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                    ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                    (by
                                      unfold nb090AlphaDummy147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                    (by
                                      unfold nb090AlphaDummy148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                    ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                    ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                    ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                    ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                    ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                    ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                    ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                    ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                    ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                    ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                    ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
                        unfold nb090AlphaDummy136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                    (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
                        unfold nb090AlphaDummy138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
                          unfold nb090AlphaDummy135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
                          unfold nb090AlphaDummy137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy141 A) from (by
                            unfold nb090AlphaDummy141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy142 h) from (by
                            unfold nb090AlphaDummy142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy139 A) from (by
                              unfold nb090AlphaDummy139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                          (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy140 h) from (by
                              unfold nb090AlphaDummy140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy129 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy131 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                                unfold nb090AlphaDummy143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                                unfold nb090AlphaDummy145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from
                                (by
                                  unfold nb090AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                              (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from
                                (by
                                  unfold nb090AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy136 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A)
                                        from (by
                                          unfold nb090AlphaDummy147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h)
                                        from (by
                                          unfold nb090AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                      ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                      ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                      ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                      ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                      ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                      ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                      ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                      ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                      ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                      ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                      ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A)
                                        from (by
                                          unfold nb090AlphaDummy147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h)
                                        from (by
                                          unfold nb090AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                      ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                      ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                      ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                      ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                      ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                      ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                      ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                      ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                      ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                      ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                      ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part030`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0006`. -/
@[expose]
noncomputable def nb090SplitAlpha0006 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
        ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy169 A))
          (synCphi (Class.cv (nb090AlphaDummy136 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy169 A))
            (synCphi (Class.cv (nb090AlphaDummy136 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy170 h))
          (synCphi (Class.cv (nb090AlphaDummy138 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy170 h))
            (synCphi (Class.cv (nb090AlphaDummy138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                      unfold nb090AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                  (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                      unfold nb090AlphaDummy145;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                        unfold nb090AlphaDummy144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                    (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                        unfold nb090AlphaDummy146;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy169 A) from (by
                          unfold nb090AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                      (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy170 h) from (by
                          unfold nb090AlphaDummy170;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy167 A) from (by
                            unfold nb090AlphaDummy167;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                        (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy168 h) from (by
                            unfold nb090AlphaDummy168;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from
                                      (by
                                        unfold nb090AlphaDummy150;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0136 A)
                                                1)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy153 h) from (by
                                        unfold nb090AlphaDummy153;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0137 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A)
                                        from (by
                                          unfold nb090AlphaDummy149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy152 h)
                                        from (by
                                          unfold nb090AlphaDummy152;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy151 A),
        (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A), (nb090AlphaDummy153 h)),
                                        ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
                                        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                        ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                        ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                                        ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                                        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                                        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                                        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                                        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                                        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                                        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                                        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                                        ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)),
        ((nb090AlphaDummy150 A), (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A),
        (nb090AlphaDummy152 h)), ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
        ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A),
        (nb090AlphaDummy146 h)), ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
        ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
        ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A),
        (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
        ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A),
        (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                unfold nb090AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                unfold nb090AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                            ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                            ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                            ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                            ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                            ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                            ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                            ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                            ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                            ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                            ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                            ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                            ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                            ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                              unfold nb090AlphaDummy147;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                          (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                              unfold nb090AlphaDummy148;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                unfold nb090AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                unfold nb090AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                            ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                            ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                            ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                            ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                            ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                            ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                            ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                            ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                            ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                            ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                            ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                            ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                            ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                        unfold nb090AlphaDummy143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                    (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                        unfold nb090AlphaDummy145;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                          unfold nb090AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                      (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                          unfold nb090AlphaDummy146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy169 A) from (by
                            unfold nb090AlphaDummy169;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                        (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy170 h) from (by
                            unfold nb090AlphaDummy170;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy167 A) from (by
                              unfold nb090AlphaDummy167;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                          (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy168 h) from (by
                              unfold nb090AlphaDummy168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy150 A) from (by
                                          unfold nb090AlphaDummy150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 1)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy153 h)
                                        from (by
                                          unfold nb090AlphaDummy153;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy151 A),
        (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A), (nb090AlphaDummy153 h)),
        ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)), ((nb090AlphaDummy147 A),
        (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
        ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)), ((nb090AlphaDummy169 A),
        (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy051 A),
        (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
        ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)), ((nb090AlphaDummy055 A),
        (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
        ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)), ((nb090AlphaDummy050 A),
        (nb090AlphaDummy053 h)), ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
        ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)), ((nb090AlphaDummy047 A),
        (nb090AlphaDummy048 h)), ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                (by
                                  unfold nb090AlphaDummy147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                (by
                                  unfold nb090AlphaDummy148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                              ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                              ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                              ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                              ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                              ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                              ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                              ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                              ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                              ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                              ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                              ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                              ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                              ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                unfold nb090AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                unfold nb090AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                (by
                                  unfold nb090AlphaDummy147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                (by
                                  unfold nb090AlphaDummy148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                              ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                              ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                              ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                              ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                              ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                              ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                              ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                              ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy051 A), (nb090AlphaDummy054 h)),
                              ((nb090AlphaDummy050 A), (nb090AlphaDummy053 h)),
                              ((nb090AlphaDummy049 A), (nb090AlphaDummy052 h)),
                              ((nb090AlphaDummy055 A), (nb090AlphaDummy056 h)),
                              ((nb090AlphaDummy047 A), (nb090AlphaDummy048 h)),
                              ((nb090AlphaDummy045 A), (nb090AlphaDummy046 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
