/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part015`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0004`. -/
@[expose]
noncomputable def nb077SplitAlpha0004 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077AlphaDummy109 F I), (nb077AlphaDummy110 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
        ((nb077AlphaDummy061 F I), (nb077AlphaDummy064 x)),
        ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)),
        ((nb077AlphaDummy065 F I), (nb077AlphaDummy066 x)),
        ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy109 F I))
          (Class.cab (nb077AlphaDummy103 F I)
            (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
              (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                (synCphi (Class.cv (nb077AlphaDummy104 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy109 F I))
            (Class.cab (nb077AlphaDummy103 F I)
              (synWrex (nb077AlphaDummy104 F I) (Class.cv (nb077AlphaDummy059 F I))
                (Wff.classEq (Class.cv (nb077AlphaDummy103 F I))
                  (synCphi (Class.cv (nb077AlphaDummy104 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077AlphaDummy110 x))
          (Class.cab (nb077AlphaDummy105 x)
            (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
              (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                (synCphi (Class.cv (nb077AlphaDummy106 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077AlphaDummy110 x))
            (Class.cab (nb077AlphaDummy105 x)
              (synWrex (nb077AlphaDummy106 x) (Class.cv (nb077AlphaDummy062 x))
                (Wff.classEq (Class.cv (nb077AlphaDummy105 x))
                  (synCphi (Class.cv (nb077AlphaDummy106 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy104 F I) from (by
                      unfold nb077AlphaDummy104;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
                  (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy106 x) from (by
                      unfold nb077AlphaDummy106;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0092 x) 1))))
                  (TAlphaVar.there
                    (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy103 F I) from (by
                        unfold nb077AlphaDummy103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
                    (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy105 x) from (by
                        unfold nb077AlphaDummy105;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0092 x) 0)))) (TAlphaVar.there
                      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy109 F I) from (by
                          unfold nb077AlphaDummy109;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0094 F I) 0))))
                      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy110 x) from (by
                          unfold nb077AlphaDummy110;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0095 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy107 F I) from (by
                            unfold nb077AlphaDummy107;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0091 F I) 0))))
                        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy108 x) from (by
                            unfold nb077AlphaDummy108;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0093 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
                              ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                    (synCplc (Class.cv (nb077AlphaDummy000 F I)) (synC1c)))
                                  (synC1st))).fv) (by decide)) (freshVar_injective
                            (((synCcnv (synC1st))).fv ∪ ((synCcom
                                  (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                                  (synC1st))).fv) (by decide)) (TAlphaVar.there
                            (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
                                    (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                      (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                        (synC1c))) (synC1st))).fv) (by decide))
                            (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
                                    (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                                    (synC1st))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
                      ((Class.cv (nb077AlphaDummy061 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077AlphaDummy062 x))).fv ∪
                      ((Class.cv (nb077AlphaDummy064 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy111 F I) from
                            (by
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
                                    (mem_lt_freshVar (nb077_support_mem_0097 x) 0))))
                          (TAlphaVar.there (show
                              (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy112 F I) from (by
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077AlphaDummy104 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077AlphaDummy106 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy118 F I) from
        (by
          unfold nb077AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I) 1)))) (show (nb077AlphaDummy113 x) ≠
        (nb077AlphaDummy121 x) from (by
          unfold nb077AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy117 F I) from (by
          unfold nb077AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I)
                  0)))) (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy120 x) from (by
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
                  (nb077_support_mem_0098 F I)
                  0)))) (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from (by
          unfold nb077AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0099 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy119 F I), (nb077AlphaDummy122 x)), ((nb077AlphaDummy118 F I),
        (nb077AlphaDummy121 x)), ((nb077AlphaDummy117 F I), (nb077AlphaDummy120 x)),
        ((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)), ((nb077AlphaDummy111 F I),
        (nb077AlphaDummy113 x)), ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
        ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
        (nb077AlphaDummy105 x)), ((nb077AlphaDummy109 F I), (nb077AlphaDummy110 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
        (nb077AlphaDummy105 x)), ((nb077AlphaDummy109 F I), (nb077AlphaDummy110 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy113 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy118
        F I) ≠ (nb077AlphaDummy129 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119
        F I) ≠ (nb077AlphaDummy131 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119
        F I) ≠ (nb077AlphaDummy131 F I) from (by
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
                                      (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I)
                                      from (by
                                        unfold nb077AlphaDummy115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0098 F I) 0)))) (show
                                      (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from
                                      (by
                                        unfold nb077AlphaDummy116;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0099 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy115 F I),
                                      (nb077AlphaDummy116 x)), ((nb077AlphaDummy111 F I),
                                      (nb077AlphaDummy113 x)), ((nb077AlphaDummy112 F I),
                                      (nb077AlphaDummy114 x)), ((nb077AlphaDummy104 F I),
                                      (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
                                      (nb077AlphaDummy105 x)), ((nb077AlphaDummy109 F I),
                                      (nb077AlphaDummy110 x)), ((nb077AlphaDummy107 F I),
                                      (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
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
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
                                    ((nb077AlphaDummy001 F I),
                                      (nb077AlphaDummy002 x F I)),
                                    ((nb077AlphaDummy004 F I),
                                      (nb077AlphaDummy006 x F I)),
                                    ((nb077AlphaDummy003 F I),
                                      (nb077AlphaDummy005 x F I))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I)
                                    from (by
                                      unfold nb077AlphaDummy115;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0098 F I)
                                              0)))) (show
                                    (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from
                                    (by
                                      unfold nb077AlphaDummy116;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0099 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I)
                                      from (by
                                        unfold nb077AlphaDummy115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0098 F I) 0)))) (show
                                      (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from
                                      (by
                                        unfold nb077AlphaDummy116;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0099 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed [((nb077AlphaDummy115 F I),
                                      (nb077AlphaDummy116 x)), ((nb077AlphaDummy111 F I),
                                      (nb077AlphaDummy113 x)), ((nb077AlphaDummy112 F I),
                                      (nb077AlphaDummy114 x)), ((nb077AlphaDummy104 F I),
                                      (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
                                      (nb077AlphaDummy105 x)), ((nb077AlphaDummy109 F I),
                                      (nb077AlphaDummy110 x)), ((nb077AlphaDummy107 F I),
                                      (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
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
                                    ((nb077AlphaDummy013 F I),
                                      (nb077AlphaDummy014 x F I)),
                                    ((nb077AlphaDummy011 F I),
                                      (nb077AlphaDummy012 x F I)),
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
                    (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy104 F I) from (by
                        unfold nb077AlphaDummy104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0090 F I) 1))))
                    (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy106 x) from (by
                        unfold nb077AlphaDummy106;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0092 x) 1)))) (TAlphaVar.there
                      (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy103 F I) from (by
                          unfold nb077AlphaDummy103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0090 F I) 0))))
                      (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy105 x) from (by
                          unfold nb077AlphaDummy105;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0092 x) 0))))
                      (TAlphaVar.there
                        (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy109 F I) from (by
                            unfold nb077AlphaDummy109;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0094 F I) 0))))
                        (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy110 x) from (by
                            unfold nb077AlphaDummy110;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0095 x) 0))))
                        (TAlphaVar.there
                          (show (nb077AlphaDummy059 F I) ≠ (nb077AlphaDummy107 F I) from
                            (by
                              unfold nb077AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0091 F I) 0))))
                          (show (nb077AlphaDummy062 x) ≠ (nb077AlphaDummy108 x) from (by
                              unfold nb077AlphaDummy108;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0093 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCcnv (synC1st))).fv ∪
                                ((synCcom (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                      (synCplc (Class.cv (nb077AlphaDummy000 F I))
                                        (synC1c))) (synC1st))).fv) (by decide))
                            (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
                                    (synCmpt x (synCvv) (synCplc (Class.cv x) (synC1c)))
                                    (synC1st))).fv) (by decide)) (TAlphaVar.there
                              (freshVar_injective (((synCcnv (synC1st))).fv ∪ ((synCcom
                                      (synCmpt (nb077AlphaDummy000 F I) (synCvv)
                                        (synCplc (Class.cv (nb077AlphaDummy000 F I))
        (synC1c))) (synC1st))).fv) (by decide)) (freshVar_injective
                                (((synCcnv (synC1st))).fv ∪ ((synCcom (synCmpt x (synCvv)
                                        (synCplc (Class.cv x) (synC1c))) (synC1st))).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077AlphaDummy059 F I))).fv ∪
                        ((Class.cv (nb077AlphaDummy061 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077AlphaDummy062 x))).fv ∪
                        ((Class.cv (nb077AlphaDummy064 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy111 F I) from (by
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
                                      (mem_lt_freshVar (nb077_support_mem_0097 x) 0))))
                            (TAlphaVar.there (show
                                (nb077AlphaDummy104 F I) ≠ (nb077AlphaDummy112 F I) from
                                (by
                                  unfold nb077AlphaDummy112;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0096 F I)
                                          1))))
                              (show (nb077AlphaDummy106 x) ≠ (nb077AlphaDummy114 x) from
                                (by
                                  unfold nb077AlphaDummy114;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0097 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077AlphaDummy104 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077AlphaDummy106 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy118 F I) from (by
          unfold nb077AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I)
                  1)))) (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy121 x) from (by
          unfold nb077AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x) 1)))) (TAlphaVar.there (show
        (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy117 F I) from (by
          unfold nb077AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0100 F I)
                  0)))) (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy120 x) from (by
          unfold nb077AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0101 x)
                  0)))) (TAlphaVar.there (show (nb077AlphaDummy111 F I) ≠
        (nb077AlphaDummy115 F I) from (by
          unfold nb077AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0098 F I)
                  0)))) (show (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from (by
          unfold nb077AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0099 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb077AlphaDummy119 F I), (nb077AlphaDummy122 x)), ((nb077AlphaDummy118 F I),
        (nb077AlphaDummy121 x)), ((nb077AlphaDummy117 F I), (nb077AlphaDummy120 x)),
        ((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)), ((nb077AlphaDummy111 F I),
        (nb077AlphaDummy113 x)), ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
        ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
        (nb077AlphaDummy105 x)), ((nb077AlphaDummy109 F I), (nb077AlphaDummy110 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)), ((nb077AlphaDummy103 F I),
        (nb077AlphaDummy105 x)), ((nb077AlphaDummy109 F I), (nb077AlphaDummy110 x)),
        ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)), ((nb077AlphaDummy061 F I),
        (nb077AlphaDummy064 x)), ((nb077AlphaDummy060 F I), (nb077AlphaDummy063 x)),
        ((nb077AlphaDummy059 F I), (nb077AlphaDummy062 x)), ((nb077AlphaDummy065 F I),
        (nb077AlphaDummy066 x)), ((nb077AlphaDummy057 F I), (nb077AlphaDummy058 x F)),
        ((nb077AlphaDummy055 F I), (nb077AlphaDummy056 x F)),
        ((nb077AlphaDummy016 F I), (nb077AlphaDummy018 x F I)),
        ((nb077AlphaDummy015 F I), (nb077AlphaDummy017 x F I)),
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
        ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
        ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
        ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077AlphaDummy111 F I))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077AlphaDummy113
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077AlphaDummy111 F I))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy118
        F I) ≠ (nb077AlphaDummy129 F I) from (by
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
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
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
        (nb077AlphaDummy113 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119
        F I) ≠ (nb077AlphaDummy131 F I) from (by
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077AlphaDummy119
        F I) ≠ (nb077AlphaDummy131 F I) from (by
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
                                        (nb077AlphaDummy111 F I) ≠
        (nb077AlphaDummy115 F I) from (by
                                          unfold nb077AlphaDummy115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0098 F I) 0)))) (show
                                        (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x)
                                        from (by
                                          unfold nb077AlphaDummy116;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0099 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)),
                                      ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
                                      ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
                                      ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
                                      ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
                                      ((nb077AlphaDummy109 F I), (nb077AlphaDummy110 x)),
                                      ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
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
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077AlphaDummy111 F I) ≠ (nb077AlphaDummy115 F I)
                                      from (by
                                        unfold nb077AlphaDummy115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0098 F I) 0)))) (show
                                      (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x) from
                                      (by
                                        unfold nb077AlphaDummy116;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0099 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077AlphaDummy111 F I) ≠
        (nb077AlphaDummy115 F I) from (by
                                          unfold nb077AlphaDummy115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0098 F I) 0)))) (show
                                        (nb077AlphaDummy113 x) ≠ (nb077AlphaDummy116 x)
                                        from (by
                                          unfold nb077AlphaDummy116;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0099 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb077AlphaDummy115 F I), (nb077AlphaDummy116 x)),
                                      ((nb077AlphaDummy111 F I), (nb077AlphaDummy113 x)),
                                      ((nb077AlphaDummy112 F I), (nb077AlphaDummy114 x)),
                                      ((nb077AlphaDummy104 F I), (nb077AlphaDummy106 x)),
                                      ((nb077AlphaDummy103 F I), (nb077AlphaDummy105 x)),
                                      ((nb077AlphaDummy109 F I), (nb077AlphaDummy110 x)),
                                      ((nb077AlphaDummy107 F I), (nb077AlphaDummy108 x)),
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
                                      ((nb077AlphaDummy013 F I),
                                        (nb077AlphaDummy014 x F I)),
                                      ((nb077AlphaDummy011 F I),
                                        (nb077AlphaDummy012 x F I)),
                                      ((nb077AlphaDummy001 F I),
                                        (nb077AlphaDummy002 x F I)),
                                      ((nb077AlphaDummy004 F I),
                                        (nb077AlphaDummy006 x F I)),
                                      ((nb077AlphaDummy003 F I),
                                        (nb077AlphaDummy005 x F I))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part016`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb077_split_alpha_0005`. -/
@[expose]
noncomputable def nb077SplitAlpha0005 (x : Var) (F : Class) (I : Class) :
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
                            ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                            ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
        ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
        ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
        (nb077AlphaDummy017 x F I)), ((nb077AlphaDummy013 F I),
        (nb077AlphaDummy014 x F I)), ((nb077AlphaDummy011 F I),
        (nb077AlphaDummy012 x F I)), ((nb077AlphaDummy001 F I),
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
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
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
                              ((nb077AlphaDummy013 F I), (nb077AlphaDummy014 x F I)),
                              ((nb077AlphaDummy011 F I), (nb077AlphaDummy012 x F I)),
                              ((nb077AlphaDummy001 F I), (nb077AlphaDummy002 x F I)),
                              ((nb077AlphaDummy004 F I), (nb077AlphaDummy006 x F I)),
                              ((nb077AlphaDummy003 F I), (nb077AlphaDummy005 x F I))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb077_compact_fv_empty_0128 (F : Class) (I : Class) :
    (nb077AlphaDummy140 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0129 (x : Var) :
    (nb077AlphaDummy143 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0130 (F : Class) (I : Class) :
    (nb077AlphaDummy139 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0131 (x : Var) :
    (nb077AlphaDummy142 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0132 (F : Class) (I : Class) :
    (nb077AlphaDummy145 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0133 (x : Var) :
    (nb077AlphaDummy146 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
