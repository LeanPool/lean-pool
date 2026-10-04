/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part003

/-! NF weak partition development: NAR4H5C093M3Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0004`. -/
@[expose]
noncomputable def nb093SplitAlpha0004 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy106 A))
          (Class.cab (nb093AlphaDummy100 A)
            (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
              (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                (synCphi (Class.cv (nb093AlphaDummy101 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy106 A))
            (Class.cab (nb093AlphaDummy100 A)
              (synWrex (nb093AlphaDummy101 A) (Class.cv (nb093AlphaDummy059 A))
                (Wff.classEq (Class.cv (nb093AlphaDummy100 A))
                  (synCphi (Class.cv (nb093AlphaDummy101 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy107 r))
          (Class.cab (nb093AlphaDummy102 r)
            (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
              (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                (synCphi (Class.cv (nb093AlphaDummy103 r))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy107 r))
            (Class.cab (nb093AlphaDummy102 r)
              (synWrex (nb093AlphaDummy103 r) (Class.cv (nb093AlphaDummy061 r))
                (Wff.classEq (Class.cv (nb093AlphaDummy102 r))
                  (synCphi (Class.cv (nb093AlphaDummy103 r))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy101 A) from (by
                      unfold nb093AlphaDummy101;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
                  (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy103 r) from (by
                      unfold nb093AlphaDummy103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))))
                  (TAlphaVar.there
                    (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy100 A) from (by
                        unfold nb093AlphaDummy100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
                    (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy102 r) from (by
                        unfold nb093AlphaDummy102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0096 r) 0)))) (TAlphaVar.there
                      (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy106 A) from (by
                          unfold nb093AlphaDummy106;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0098 A) 0))))
                      (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy107 r) from (by
                          unfold nb093AlphaDummy107;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0099 r) 0))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy104 A) from (by
                            unfold nb093AlphaDummy104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0095 A) 0))))
                        (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy105 r) from (by
                            unfold nb093AlphaDummy105;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0097 r) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb093AlphaDummy059 A))).fv ∪
                      ((Class.cv (nb093AlphaDummy058 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb093AlphaDummy061 r))).fv ∪
                      ((Class.cv (nb093AlphaDummy060 r))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy108 A) from (by
                              unfold nb093AlphaDummy108;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                          (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy110 r) from (by
                              unfold nb093AlphaDummy110;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0101 r) 0))))
                          (TAlphaVar.there
                            (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy109 A) from (by
                                unfold nb093AlphaDummy109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                            (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy111 r) from (by
                                unfold nb093AlphaDummy111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0101 r) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093AlphaDummy101 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb093AlphaDummy103 r))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy115 A) from (by
          unfold nb093AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 1)))) (show (nb093AlphaDummy110 r) ≠
        (nb093AlphaDummy118 r) from (by
          unfold nb093AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy114 A) from (by
          unfold nb093AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 0)))) (show (nb093AlphaDummy110 r) ≠
        (nb093AlphaDummy117 r) from (by
          unfold nb093AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from (by
          unfold nb093AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A)
                  0)))) (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from (by
          unfold nb093AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy116 A), (nb093AlphaDummy119 r)), ((nb093AlphaDummy115 A),
        (nb093AlphaDummy118 r)), ((nb093AlphaDummy114 A), (nb093AlphaDummy117 r)),
        ((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)), ((nb093AlphaDummy108 A),
        (nb093AlphaDummy110 r)), ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
        ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A),
        (nb093AlphaDummy102 r)), ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy116 A), (nb093AlphaDummy119 r)), ((nb093AlphaDummy115 A),
        (nb093AlphaDummy118 r)), ((nb093AlphaDummy114 A), (nb093AlphaDummy117 r)),
        ((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)), ((nb093AlphaDummy108 A),
        (nb093AlphaDummy110 r)), ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
        ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A),
        (nb093AlphaDummy102 r)), ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy110
        r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy116
        A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy116
        A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from
                                      (by
                                        unfold nb093AlphaDummy112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0102 A)
                                                0)))) (show (nb093AlphaDummy110 r) ≠
                                        (nb093AlphaDummy113 r) from (by
                                        unfold nb093AlphaDummy113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0103 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                                    ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                                    ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                                    ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                                    ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                                    ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
                                    ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                                    ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                    ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                    ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                    ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                    ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                    ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                    ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                    ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                    ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                    ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                    ((nb093AlphaDummy000 A), d),
                                    ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
                                      (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
                                      (nb093AlphaDummy005 A r d)),
                                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from
                                    (by
                                      unfold nb093AlphaDummy112;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0102 A)
                                              0)))) (show
                                    (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from
                                    (by
                                      unfold nb093AlphaDummy113;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0103 r)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from
                                      (by
                                        unfold nb093AlphaDummy112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0102 A)
                                                0)))) (show (nb093AlphaDummy110 r) ≠
                                        (nb093AlphaDummy113 r) from (by
                                        unfold nb093AlphaDummy113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0103 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                                    ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                                    ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                                    ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                                    ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                                    ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
                                    ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                                    ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                    ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                    ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                    ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                    ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                    ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                    ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                    ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                    ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                    ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                    ((nb093AlphaDummy000 A), d),
                                    ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
                                      (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
                                      (nb093AlphaDummy005 A r d)),
                                    ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy101 A) from (by
                        unfold nb093AlphaDummy101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
                    (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy103 r) from (by
                        unfold nb093AlphaDummy103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0096 r) 1)))) (TAlphaVar.there
                      (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy100 A) from (by
                          unfold nb093AlphaDummy100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
                      (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy102 r) from (by
                          unfold nb093AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0096 r) 0))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy106 A) from (by
                            unfold nb093AlphaDummy106;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0098 A) 0))))
                        (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy107 r) from (by
                            unfold nb093AlphaDummy107;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0099 r) 0))))
                        (TAlphaVar.there
                          (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy104 A) from (by
                              unfold nb093AlphaDummy104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0095 A) 0))))
                          (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy105 r) from (by
                              unfold nb093AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0097 r) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb093AlphaDummy059 A))).fv ∪
                        ((Class.cv (nb093AlphaDummy058 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093AlphaDummy061 r))).fv ∪
                        ((Class.cv (nb093AlphaDummy060 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy108 A) from (by
                                unfold nb093AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                            (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy110 r) from (by
                                unfold nb093AlphaDummy110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0101 r) 0))))
                            (TAlphaVar.there
                              (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy109 A) from
                                (by
                                  unfold nb093AlphaDummy109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                              (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy111 r) from
                                (by
                                  unfold nb093AlphaDummy111;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0101 r) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093AlphaDummy101 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb093AlphaDummy103 r))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy115 A) from (by
          unfold nb093AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 1)))) (show (nb093AlphaDummy110 r) ≠
        (nb093AlphaDummy118 r) from (by
          unfold nb093AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy114 A) from (by
          unfold nb093AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A)
                  0)))) (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy117 r) from (by
          unfold nb093AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy108 A) ≠
        (nb093AlphaDummy112 A) from (by
          unfold nb093AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A)
                  0)))) (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from (by
          unfold nb093AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy116 A), (nb093AlphaDummy119 r)), ((nb093AlphaDummy115 A),
        (nb093AlphaDummy118 r)), ((nb093AlphaDummy114 A), (nb093AlphaDummy117 r)),
        ((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)), ((nb093AlphaDummy108 A),
        (nb093AlphaDummy110 r)), ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
        ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A),
        (nb093AlphaDummy102 r)), ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy116 A), (nb093AlphaDummy119 r)), ((nb093AlphaDummy115 A),
        (nb093AlphaDummy118 r)), ((nb093AlphaDummy114 A), (nb093AlphaDummy117 r)),
        ((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)), ((nb093AlphaDummy108 A),
        (nb093AlphaDummy110 r)), ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
        ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A),
        (nb093AlphaDummy102 r)), ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy110 r))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy115
        A) ≠ (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy116
        A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy116
        A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A)
                                        from (by
                                          unfold nb093AlphaDummy112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0102 A) 0)))) (show
                                        (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r)
                                        from (by
                                          unfold nb093AlphaDummy113;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0103 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                                      ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                                      ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                                      ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                                      ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                                      ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
                                      ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                                      ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                      ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                      ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                      ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                      ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                      ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                      ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                      ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                      ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                      ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                      ((nb093AlphaDummy000 A), d),
                                      ((nb093AlphaDummy001 A), r),
                                      ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                                      ((nb093AlphaDummy004 A),
                                        (nb093AlphaDummy005 A r d)),
                                      ((nb093AlphaDummy002 A),
                                        (nb093AlphaDummy003 A r d))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from
                                      (by
                                        unfold nb093AlphaDummy112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0102 A)
                                                0)))) (show (nb093AlphaDummy110 r) ≠
                                        (nb093AlphaDummy113 r) from (by
                                        unfold nb093AlphaDummy113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0103 r)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A)
                                        from (by
                                          unfold nb093AlphaDummy112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0102 A) 0)))) (show
                                        (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r)
                                        from (by
                                          unfold nb093AlphaDummy113;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0103 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                                      ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                                      ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                                      ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                                      ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                                      ((nb093AlphaDummy106 A), (nb093AlphaDummy107 r)),
                                      ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                                      ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                      ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                      ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                      ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                      ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                      ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                      ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                                      ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                      ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                                      ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                      ((nb093AlphaDummy000 A), d),
                                      ((nb093AlphaDummy001 A), r),
                                      ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                                      ((nb093AlphaDummy004 A),
                                        (nb093AlphaDummy005 A r d)),
                                      ((nb093AlphaDummy002 A),
                                        (nb093AlphaDummy003 A r d))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0005`. -/
@[expose]
noncomputable def nb093SplitAlpha0005 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)),
        ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)),
        ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
        ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
        ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)),
        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy134 A))
          (synCphi (Class.cv (nb093AlphaDummy101 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy134 A))
            (synCphi (Class.cv (nb093AlphaDummy101 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy135 r))
          (synCphi (Class.cv (nb093AlphaDummy103 r)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy135 r))
            (synCphi (Class.cv (nb093AlphaDummy103 r)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy108 A) from (by
                      unfold nb093AlphaDummy108;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                  (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy110 r) from (by
                      unfold nb093AlphaDummy110;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0101 r) 0))))
                  (TAlphaVar.there
                    (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy109 A) from (by
                        unfold nb093AlphaDummy109;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                    (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy111 r) from (by
                        unfold nb093AlphaDummy111;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0101 r) 1)))) (TAlphaVar.there
                      (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy134 A) from (by
                          unfold nb093AlphaDummy134;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0130 A) 0))))
                      (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy135 r) from (by
                          unfold nb093AlphaDummy135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0131 r) 0))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy132 A) from (by
                            unfold nb093AlphaDummy132;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0128 A) 0))))
                        (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy133 r) from (by
                            unfold nb093AlphaDummy133;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0129 r) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy101 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy103 r))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy115 A) from
                                      (by
                                        unfold nb093AlphaDummy115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0104 A)
                                                1)))) (show (nb093AlphaDummy110 r) ≠
                                        (nb093AlphaDummy118 r) from (by
                                        unfold nb093AlphaDummy118;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0105 r)
                                                1)))) (TAlphaVar.there (show
                                        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy114 A)
                                        from (by
                                          unfold nb093AlphaDummy114;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0104 A) 0)))) (show
                                        (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy117 r)
                                        from (by
                                          unfold nb093AlphaDummy117;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0105 r) 0))))
                                      (TAlphaVar.there (show (nb093AlphaDummy108 A) ≠
        (nb093AlphaDummy112 A) from (by
          unfold nb093AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A) 0)))) (show (nb093AlphaDummy110 r) ≠
        (nb093AlphaDummy113 r) from (by
          unfold nb093AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb093AlphaDummy116 A),
        (nb093AlphaDummy119 r)), ((nb093AlphaDummy115 A), (nb093AlphaDummy118 r)),
                                        ((nb093AlphaDummy114 A), (nb093AlphaDummy117 r)),
                                        ((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                                        ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                                        ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                                        ((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)),
                                        ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)),
                                        ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                                        ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                                        ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)),
                                        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                                        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                                        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                                        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                                        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                                        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                                        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                                        ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                                        ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                                        ((nb093AlphaDummy000 A), d),
                                        ((nb093AlphaDummy001 A), r),
                                        ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb093AlphaDummy116 A), (nb093AlphaDummy119 r)),
        ((nb093AlphaDummy115 A), (nb093AlphaDummy118 r)), ((nb093AlphaDummy114 A),
        (nb093AlphaDummy117 r)), ((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
        ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)), ((nb093AlphaDummy109 A),
        (nb093AlphaDummy111 r)), ((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)),
        ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)), ((nb093AlphaDummy101 A),
        (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
        ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)), ((nb093AlphaDummy104 A),
        (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from (by
                                unfold nb093AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                            (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from (by
                                unfold nb093AlphaDummy113;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                            ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                            ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                            ((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)),
                            ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)),
                            ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                            ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                            ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)),
                            ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                            ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                            ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                            ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                            ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                            ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                            ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                            ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                            ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                            ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                            ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                            ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                            ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                            ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                            ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from (by
                              unfold nb093AlphaDummy112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                          (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from (by
                              unfold nb093AlphaDummy113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from (by
                                unfold nb093AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                            (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from (by
                                unfold nb093AlphaDummy113;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                            ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                            ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                            ((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)),
                            ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)),
                            ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                            ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                            ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)),
                            ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                            ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                            ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                            ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                            ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                            ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                            ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                            ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                            ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                            ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                            ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                            ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                            ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                            ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                            ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy108 A) from (by
                        unfold nb093AlphaDummy108;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                    (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy110 r) from (by
                        unfold nb093AlphaDummy110;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0101 r) 0)))) (TAlphaVar.there
                      (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy109 A) from (by
                          unfold nb093AlphaDummy109;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                      (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy111 r) from (by
                          unfold nb093AlphaDummy111;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0101 r) 1))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy134 A) from (by
                            unfold nb093AlphaDummy134;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0130 A) 0))))
                        (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy135 r) from (by
                            unfold nb093AlphaDummy135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0131 r) 0))))
                        (TAlphaVar.there
                          (show (nb093AlphaDummy101 A) ≠ (nb093AlphaDummy132 A) from (by
                              unfold nb093AlphaDummy132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0128 A) 0))))
                          (show (nb093AlphaDummy103 r) ≠ (nb093AlphaDummy133 r) from (by
                              unfold nb093AlphaDummy133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0129 r) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb093AlphaDummy101 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093AlphaDummy103 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb093AlphaDummy108 A) ≠
        (nb093AlphaDummy115 A) from (by
                                          unfold nb093AlphaDummy115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0104 A) 1)))) (show
                                        (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy118 r)
                                        from (by
                                          unfold nb093AlphaDummy118;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0105 r) 1))))
                                      (TAlphaVar.there (show (nb093AlphaDummy108 A) ≠
        (nb093AlphaDummy114 A) from (by
          unfold nb093AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 0)))) (show (nb093AlphaDummy110 r) ≠
        (nb093AlphaDummy117 r) from (by
          unfold nb093AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from (by
          unfold nb093AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A) 0)))) (show (nb093AlphaDummy110 r) ≠
        (nb093AlphaDummy113 r) from (by
          unfold nb093AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb093AlphaDummy116 A),
        (nb093AlphaDummy119 r)), ((nb093AlphaDummy115 A), (nb093AlphaDummy118 r)),
        ((nb093AlphaDummy114 A), (nb093AlphaDummy117 r)), ((nb093AlphaDummy112 A),
        (nb093AlphaDummy113 r)), ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
        ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)), ((nb093AlphaDummy134 A),
        (nb093AlphaDummy135 r)), ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)),
        ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A),
        (nb093AlphaDummy102 r)), ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)),
        ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A),
        (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
        ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A),
        (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A),
        (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A),
        (nb093AlphaDummy049 r d)), ((nb093AlphaDummy000 A), d),
        ((nb093AlphaDummy001 A), r), ((nb093AlphaDummy006 A),
        (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy122 A) from (by
          unfold
            nb093AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy123 r) from (by
          unfold
            nb093AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy120 A) from (by
          unfold
            nb093AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy121 r) from (by
          unfold
            nb093AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy116 A), (nb093AlphaDummy119 r)), ((nb093AlphaDummy115 A),
        (nb093AlphaDummy118 r)), ((nb093AlphaDummy114 A), (nb093AlphaDummy117 r)),
        ((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)), ((nb093AlphaDummy108 A),
        (nb093AlphaDummy110 r)), ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
        ((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)), ((nb093AlphaDummy132 A),
        (nb093AlphaDummy133 r)), ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
        ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)), ((nb093AlphaDummy130 A),
        (nb093AlphaDummy131 r)), ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
        ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)), ((nb093AlphaDummy058 A),
        (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
        ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)), ((nb093AlphaDummy054 A),
        (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)), ((nb093AlphaDummy044 A),
        (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠ (nb093AlphaDummy126 A) from (by
          unfold
            nb093AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy127 r) from (by
          unfold
            nb093AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy115 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093AlphaDummy118 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy108
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy110 r))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy116 A) ≠ (nb093AlphaDummy128 A) from (by
          unfold
            nb093AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy129 r) from (by
          unfold
            nb093AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy116 A) ≠
        (nb093AlphaDummy124 A) from (by
          unfold
            nb093AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093AlphaDummy119 r) ≠ (nb093AlphaDummy125 r) from (by
          unfold
            nb093AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from
                                (by
                                  unfold nb093AlphaDummy112;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                              (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from
                                (by
                                  unfold nb093AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                              ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                              ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                              ((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)),
                              ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)),
                              ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                              ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                              ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)),
                              ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                              ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                              ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                              ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                              ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                              ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                              ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                              ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                              ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                              ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                              ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                              ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                              ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                              ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                              ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from (by
                                unfold nb093AlphaDummy112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                            (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from (by
                                unfold nb093AlphaDummy113;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093AlphaDummy108 A) ≠ (nb093AlphaDummy112 A) from
                                (by
                                  unfold nb093AlphaDummy112;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                              (show (nb093AlphaDummy110 r) ≠ (nb093AlphaDummy113 r) from
                                (by
                                  unfold nb093AlphaDummy113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb093AlphaDummy112 A), (nb093AlphaDummy113 r)),
                              ((nb093AlphaDummy108 A), (nb093AlphaDummy110 r)),
                              ((nb093AlphaDummy109 A), (nb093AlphaDummy111 r)),
                              ((nb093AlphaDummy134 A), (nb093AlphaDummy135 r)),
                              ((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)),
                              ((nb093AlphaDummy101 A), (nb093AlphaDummy103 r)),
                              ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
                              ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)),
                              ((nb093AlphaDummy104 A), (nb093AlphaDummy105 r)),
                              ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
                              ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)),
                              ((nb093AlphaDummy062 A), (nb093AlphaDummy063 r)),
                              ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
                              ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
                              ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
                              ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
                              ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
                              ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
                              ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
                              ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
                              ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
                              ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
                              ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb093_split_alpha_0006`. -/
@[expose]
noncomputable def nb093SplitAlpha0006 (A : Class) (r : Var) (d : Var)
    (dv_d_r : d ≠ r) :
    TAlphaWff
      [((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)),
        ((nb093AlphaDummy052 A), (nb093AlphaDummy053 r)),
        ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)),
        ((nb093AlphaDummy050 A), (nb093AlphaDummy051 r d)),
        ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)),
        ((nb093AlphaDummy004 A), (nb093AlphaDummy005 A r d)),
        ((nb093AlphaDummy002 A), (nb093AlphaDummy003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy056 A))
          (synCcnv (Class.cv (nb093AlphaDummy001 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy056 A))
            (synCcnv (Class.cv (nb093AlphaDummy001 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093AlphaDummy057 r)) (synCcnv (Class.cv r)))
        (Wff.neg
          (Wff.classMem (Class.cv (nb093AlphaDummy057 r)) (synCcnv (Class.cv r))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy062 A) from (by
                          unfold nb093AlphaDummy062;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0054 A) 0))))) (Ne.symm
                      (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy063 r) from (by
                          unfold nb093AlphaDummy063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0055 r) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy062 A) from (by
                            unfold nb093AlphaDummy062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0052 A) 0))))) (Ne.symm
                        (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy063 r) from (by
                            unfold nb093AlphaDummy063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0053 r) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0002 A r d)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy065 A) from (by
          unfold nb093AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093AlphaDummy061 r) ≠
        (nb093AlphaDummy067 r) from (by
          unfold nb093AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 0)))) (show (nb093AlphaDummy061 r) ≠
        (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy094 A) from (by
          unfold nb093AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy095 r) from (by
          unfold nb093AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠
        (nb093AlphaDummy068 A) from (by
          unfold nb093AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy069 r) from (by
          unfold nb093AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy058 A))).fv ∪
        ((Class.cv (nb093AlphaDummy059 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)), ((nb093AlphaDummy065 A),
        (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
        ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)), ((nb093AlphaDummy068 A),
        (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy065 A) from (by
          unfold nb093AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093AlphaDummy061 r) ≠
        (nb093AlphaDummy067 r) from (by
          unfold nb093AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 0)))) (show (nb093AlphaDummy061 r) ≠
        (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy094 A) from (by
          unfold nb093AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy095 r) from (by
          unfold nb093AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠
        (nb093AlphaDummy068 A) from (by
          unfold nb093AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy069 r) from (by
          unfold nb093AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy058 A))).fv ∪
        ((Class.cv (nb093AlphaDummy059 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)), ((nb093AlphaDummy065 A),
        (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
        ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)), ((nb093AlphaDummy068 A),
        (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0004 A r d)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy101 A) from (by
          unfold nb093AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093AlphaDummy060 r) ≠
        (nb093AlphaDummy103 r) from (by
          unfold nb093AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 0)))) (show (nb093AlphaDummy060 r) ≠
        (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy130 A) from (by
          unfold nb093AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy131 r) from (by
          unfold nb093AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠
        (nb093AlphaDummy104 A) from (by
          unfold nb093AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy105 r) from (by
          unfold nb093AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy001 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv r)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy061 r))).fv ∪
        ((Class.cv (nb093AlphaDummy060 r))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)), ((nb093AlphaDummy101 A),
        (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
        ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)), ((nb093AlphaDummy104 A),
        (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy101 A) from (by
          unfold nb093AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093AlphaDummy060 r) ≠
        (nb093AlphaDummy103 r) from (by
          unfold nb093AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 0)))) (show (nb093AlphaDummy060 r) ≠
        (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 0)))) (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy130 A) from (by
          unfold nb093AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy131 r) from (by
          unfold nb093AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠
        (nb093AlphaDummy104 A) from (by
          unfold nb093AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy105 r) from (by
          unfold nb093AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093AlphaDummy001 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv r)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv (nb093AlphaDummy058 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093AlphaDummy061 r))).fv ∪
        ((Class.cv (nb093AlphaDummy060 r))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)), ((nb093AlphaDummy101 A),
        (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
        ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)), ((nb093AlphaDummy104 A),
        (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                    (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy059 A) from (by
                        unfold nb093AlphaDummy059;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0136 A) 1))))
                    (show r ≠ (nb093AlphaDummy061 r) from (by
                        unfold nb093AlphaDummy061;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0137 r) 1)))) (TAlphaVar.there
                      (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy058 A) from (by
                          unfold nb093AlphaDummy058;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0136 A) 0))))
                      (show r ≠ (nb093AlphaDummy060 r) from (by
                          unfold nb093AlphaDummy060;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0137 r) 0))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy062 A) from (by
                            unfold nb093AlphaDummy062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0134 A) 0))))
                        (show r ≠ (nb093AlphaDummy063 r) from (by
                            unfold nb093AlphaDummy063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0135 r) 0))))
                        (TAlphaVar.there
                          (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy056 A) from (by
                              unfold nb093AlphaDummy056;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0132 A) 0))))
                          (show r ≠ (nb093AlphaDummy057 r) from (by
                              unfold nb093AlphaDummy057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0133 r) 0))))
                          (TAlphaVar.there
                            (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy054 A) from (by
                                unfold nb093AlphaDummy054;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0050 A) 0))))
                            (show r ≠ (nb093AlphaDummy055 r) from (by
                                unfold nb093AlphaDummy055;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0051 r) 0))))
                            (TAlphaVar.there
                              (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy052 A) from
                                (by
                                  unfold nb093AlphaDummy052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0048 A) 0))))
                              (show r ≠ (nb093AlphaDummy053 r) from (by
                                  unfold nb093AlphaDummy053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0049 r) 0))))
                              (TAlphaVar.there (show
                                  (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy045 A) from (by
                                    unfold nb093AlphaDummy045;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0042 A)
                                            1)))) (show r ≠ (nb093AlphaDummy047 r d) from (by
                                    unfold nb093AlphaDummy047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0044 r d)
                                            1)))) (TAlphaVar.there (show
                                    (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy044 A) from
                                    (by
                                      unfold nb093AlphaDummy044;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0042 A)
                                              0)))) (show r ≠ (nb093AlphaDummy046 r d) from
                                    (by
                                      unfold nb093AlphaDummy046;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0044 r d)
                                              0)))) (TAlphaVar.there (show
                                      (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy050 A) from
                                      (by
                                        unfold nb093AlphaDummy050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0046 A)
                                                0)))) (show r ≠ (nb093AlphaDummy051 r d) from
                                      (by
                                        unfold nb093AlphaDummy051;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0047 r d) 0))))
                                    (TAlphaVar.there (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy048 A) from (by
                                          unfold nb093AlphaDummy048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0043 A) 0))))
                                      (show r ≠ (nb093AlphaDummy049 r d) from (by
                                          unfold nb093AlphaDummy049;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0045 r d) 0))))
                                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                        (Ne.symm dv_d_r)
                                        (TAlphaVar.here _ _ _))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                      (Ne.symm (show (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy062 A) from
                          (by
                            unfold nb093AlphaDummy062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0054 A) 0))))) (Ne.symm
                        (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy063 r) from (by
                            unfold nb093AlphaDummy063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0055 r) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy062 A) from (by
                              unfold nb093AlphaDummy062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0052 A) 0))))) (Ne.symm
                          (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy063 r) from (by
                              unfold nb093AlphaDummy063;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0053 r) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb093SplitAlpha0002 A r d)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy065 A) from (by
          unfold nb093AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093AlphaDummy061 r) ≠
        (nb093AlphaDummy067 r) from (by
          unfold nb093AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠
        (nb093AlphaDummy094 A) from (by
          unfold nb093AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy095 r) from (by
          unfold nb093AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠
        (nb093AlphaDummy068 A) from (by
          unfold nb093AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy069 r) from (by
          unfold nb093AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy058 A))).fv ∪
        ((Class.cv (nb093AlphaDummy059 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)), ((nb093AlphaDummy065 A),
        (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
        ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)), ((nb093AlphaDummy068 A),
        (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy065 A) from (by
          unfold nb093AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093AlphaDummy061 r) ≠
        (nb093AlphaDummy067 r) from (by
          unfold nb093AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy059 A) ≠ (nb093AlphaDummy064 A) from (by
          unfold nb093AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy066 r) from (by
          unfold nb093AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠
        (nb093AlphaDummy094 A) from (by
          unfold nb093AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy095 r) from (by
          unfold nb093AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy059 A) ≠
        (nb093AlphaDummy068 A) from (by
          unfold nb093AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093AlphaDummy061 r) ≠ (nb093AlphaDummy069 r) from (by
          unfold nb093AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy058 A))).fv ∪
        ((Class.cv (nb093AlphaDummy059 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy060 r))).fv ∪ ((Class.cv (nb093AlphaDummy061 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy096 A), (nb093AlphaDummy097 r)), ((nb093AlphaDummy065 A),
        (nb093AlphaDummy067 r)), ((nb093AlphaDummy064 A), (nb093AlphaDummy066 r)),
        ((nb093AlphaDummy094 A), (nb093AlphaDummy095 r)), ((nb093AlphaDummy068 A),
        (nb093AlphaDummy069 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb093SplitAlpha0004 A r d)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy101 A) from (by
          unfold nb093AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093AlphaDummy060 r) ≠
        (nb093AlphaDummy103 r) from (by
          unfold nb093AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠
        (nb093AlphaDummy130 A) from (by
          unfold nb093AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy131 r) from (by
          unfold nb093AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠
        (nb093AlphaDummy104 A) from (by
          unfold nb093AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy105 r) from (by
          unfold nb093AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy001
        A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv
        (nb093AlphaDummy058 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)), ((nb093AlphaDummy101 A),
        (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
        ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)), ((nb093AlphaDummy104 A),
        (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy101 A) from (by
          unfold nb093AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093AlphaDummy060 r) ≠
        (nb093AlphaDummy103 r) from (by
          unfold nb093AlphaDummy103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093AlphaDummy058 A) ≠ (nb093AlphaDummy100 A) from (by
          unfold nb093AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy102 r) from (by
          unfold nb093AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠
        (nb093AlphaDummy130 A) from (by
          unfold nb093AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy131 r) from (by
          unfold nb093AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093AlphaDummy058 A) ≠
        (nb093AlphaDummy104 A) from (by
          unfold nb093AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093AlphaDummy060 r) ≠ (nb093AlphaDummy105 r) from (by
          unfold nb093AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093AlphaDummy001
        A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093AlphaDummy059 A))).fv ∪ ((Class.cv
        (nb093AlphaDummy058 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093AlphaDummy061 r))).fv ∪ ((Class.cv (nb093AlphaDummy060 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093SplitAlpha0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb093AlphaDummy132 A), (nb093AlphaDummy133 r)), ((nb093AlphaDummy101 A),
        (nb093AlphaDummy103 r)), ((nb093AlphaDummy100 A), (nb093AlphaDummy102 r)),
        ((nb093AlphaDummy130 A), (nb093AlphaDummy131 r)), ((nb093AlphaDummy104 A),
        (nb093AlphaDummy105 r)), ((nb093AlphaDummy059 A), (nb093AlphaDummy061 r)),
        ((nb093AlphaDummy058 A), (nb093AlphaDummy060 r)), ((nb093AlphaDummy062 A),
        (nb093AlphaDummy063 r)), ((nb093AlphaDummy056 A), (nb093AlphaDummy057 r)),
        ((nb093AlphaDummy054 A), (nb093AlphaDummy055 r)), ((nb093AlphaDummy052 A),
        (nb093AlphaDummy053 r)), ((nb093AlphaDummy045 A), (nb093AlphaDummy047 r d)),
        ((nb093AlphaDummy044 A), (nb093AlphaDummy046 r d)), ((nb093AlphaDummy050 A),
        (nb093AlphaDummy051 r d)), ((nb093AlphaDummy048 A), (nb093AlphaDummy049 r d)),
        ((nb093AlphaDummy000 A), d), ((nb093AlphaDummy001 A), r),
        ((nb093AlphaDummy006 A), (nb093AlphaDummy007 r d)), ((nb093AlphaDummy004 A),
        (nb093AlphaDummy005 A r d)), ((nb093AlphaDummy002 A),
        (nb093AlphaDummy003 A r d))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                      (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy059 A) from (by
                          unfold nb093AlphaDummy059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0136 A) 1))))
                      (show r ≠ (nb093AlphaDummy061 r) from (by
                          unfold nb093AlphaDummy061;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0137 r) 1))))
                      (TAlphaVar.there
                        (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy058 A) from (by
                            unfold nb093AlphaDummy058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0136 A) 0))))
                        (show r ≠ (nb093AlphaDummy060 r) from (by
                            unfold nb093AlphaDummy060;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0137 r) 0))))
                        (TAlphaVar.there
                          (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy062 A) from (by
                              unfold nb093AlphaDummy062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0134 A) 0))))
                          (show r ≠ (nb093AlphaDummy063 r) from (by
                              unfold nb093AlphaDummy063;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0135 r) 0))))
                          (TAlphaVar.there
                            (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy056 A) from (by
                                unfold nb093AlphaDummy056;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0132 A) 0))))
                            (show r ≠ (nb093AlphaDummy057 r) from (by
                                unfold nb093AlphaDummy057;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0133 r) 0))))
                            (TAlphaVar.there
                              (show (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy054 A) from
                                (by
                                  unfold nb093AlphaDummy054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0050 A) 0))))
                              (show r ≠ (nb093AlphaDummy055 r) from (by
                                  unfold nb093AlphaDummy055;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0051 r) 0))))
                              (TAlphaVar.there (show
                                  (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy052 A) from (by
                                    unfold nb093AlphaDummy052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0048 A)
                                            0)))) (show r ≠ (nb093AlphaDummy053 r) from (by
                                    unfold nb093AlphaDummy053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0049 r)
                                            0)))) (TAlphaVar.there (show
                                    (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy045 A) from
                                    (by
                                      unfold nb093AlphaDummy045;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0042 A)
                                              1)))) (show r ≠ (nb093AlphaDummy047 r d) from
                                    (by
                                      unfold nb093AlphaDummy047;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0044 r d)
                                              1)))) (TAlphaVar.there (show
                                      (nb093AlphaDummy001 A) ≠ (nb093AlphaDummy044 A) from
                                      (by
                                        unfold nb093AlphaDummy044;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0042 A)
                                                0)))) (show r ≠ (nb093AlphaDummy046 r d) from
                                      (by
                                        unfold nb093AlphaDummy046;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0044 r d) 0))))
                                    (TAlphaVar.there (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy050 A) from (by
                                          unfold nb093AlphaDummy050;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0046 A) 0))))
                                      (show r ≠ (nb093AlphaDummy051 r d) from (by
                                          unfold nb093AlphaDummy051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0047 r d) 0))))
                                      (TAlphaVar.there (show (nb093AlphaDummy001 A) ≠
        (nb093AlphaDummy048 A) from (by
          unfold nb093AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093AlphaDummy049 r d) from
        (by
          unfold nb093AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r)
        (TAlphaVar.here _ _ _)))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
