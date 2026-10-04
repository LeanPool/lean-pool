/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C096M3Part003

/-! NF weak partition development: NAR4H5C096M3Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb096_split_alpha_0005`. -/
@[expose]
noncomputable def nb096SplitAlpha0005 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy102 D R))
          (Class.cv (nb096AlphaDummy041 D R))) (Wff.neg
          (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
            (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy104 D R q))
          (Class.cv (nb096AlphaDummy043 D R q))) (Wff.neg
          (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
            (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy041 D R) ≠ (nb096AlphaDummy102 D R) from
            (by
              unfold nb096AlphaDummy102;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 1))))
          (show (nb096AlphaDummy043 D R q) ≠ (nb096AlphaDummy104 D R q) from (by
              unfold nb096AlphaDummy104;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 1))))
          (TAlphaVar.there (show (nb096AlphaDummy041 D R) ≠ (nb096AlphaDummy101 D R) from
              (by
                unfold nb096AlphaDummy101;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 0))))
            (show (nb096AlphaDummy043 D R q) ≠ (nb096AlphaDummy103 D R q) from (by
                unfold nb096AlphaDummy103;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 0))))
            (TAlphaVar.there
              (show (nb096AlphaDummy041 D R) ≠ (nb096AlphaDummy131 D R) from (by
                  unfold nb096AlphaDummy131;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0130 D R) 0))))
              (show (nb096AlphaDummy043 D R q) ≠ (nb096AlphaDummy132 D R q) from (by
                  unfold nb096AlphaDummy132;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0131 D R q) 0))))
              (TAlphaVar.there
                (show (nb096AlphaDummy041 D R) ≠ (nb096AlphaDummy105 D R) from (by
                    unfold nb096AlphaDummy105;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0127 D R) 0))))
                (show (nb096AlphaDummy043 D R q) ≠ (nb096AlphaDummy106 D R q) from (by
                    unfold nb096AlphaDummy106;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb096_support_mem_0129 D R q) 0)))) (TAlphaVar.there
                  (freshVar_injective (((synCen)).fv ∪ ((synCsn (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                                  (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
                    (by decide)) (freshVar_injective (((synCen)).fv ∪ ((synCsn (synCin D
                            (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (synCuni (synCuni (Class.cv q)))))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
                ((Class.cv (nb096AlphaDummy041 D R))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
                ((Class.cv (nb096AlphaDummy043 D R q))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096AlphaDummy102 D R) ≠ (nb096AlphaDummy109 D R)
                                      from (by
                                        unfold nb096AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 0)))) (show
                                      (nb096AlphaDummy104 D R q) ≠
                                        (nb096AlphaDummy111 D R q) from (by
                                        unfold nb096AlphaDummy111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 0))))
                                    (TAlphaVar.there (show (nb096AlphaDummy102 D R) ≠
        (nb096AlphaDummy110 D R) from (by
                                          unfold nb096AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0104 D R) 1)))) (show
                                        (nb096AlphaDummy104 D R q) ≠
        (nb096AlphaDummy112 D R q) from (by
                                          unfold nb096AlphaDummy112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0105 D R q) 1))))
                                      (TAlphaVar.there (show (nb096AlphaDummy102 D R) ≠
        (nb096AlphaDummy135 D R) from (by
          unfold nb096AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0134 D R) 0)))) (show (nb096AlphaDummy104 D R q) ≠
        (nb096AlphaDummy136 D R q) from (by
          unfold nb096AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0135 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy102 D R) ≠ (nb096AlphaDummy133 D R) from (by
          unfold nb096AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0132 D R) 0)))) (show (nb096AlphaDummy104 D R q) ≠
        (nb096AlphaDummy134 D R q) from (by
          unfold nb096AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0133 D R q) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb096AlphaDummy102 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb096AlphaDummy104 D R q))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy116 D R) from
        (by
          unfold nb096AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  1)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy119 D R q) from
        (by
          unfold nb096AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy115 D R) from (by
          unfold nb096AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy118 D R q) from
        (by
          unfold nb096AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold
            nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold
            nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy116
        D R) ≠ (nb096AlphaDummy127 D R) from (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy116
        D R) ≠ (nb096AlphaDummy127 D R) from (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠ (nb096AlphaDummy129 D R) from
        (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy129 D R) from (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy113 D R) from
        (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb096AlphaDummy102 D R) ≠ (nb096AlphaDummy109 D R)
                                      from (by
                                        unfold nb096AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 0)))) (show
                                      (nb096AlphaDummy104 D R q) ≠
                                        (nb096AlphaDummy111 D R q) from (by
                                        unfold nb096AlphaDummy111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 0))))
                                    (TAlphaVar.there (show (nb096AlphaDummy102 D R) ≠
        (nb096AlphaDummy110 D R) from (by
                                          unfold nb096AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0104 D R) 1)))) (show
                                        (nb096AlphaDummy104 D R q) ≠
        (nb096AlphaDummy112 D R q) from (by
                                          unfold nb096AlphaDummy112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb096_support_mem_0105 D R q) 1))))
                                      (TAlphaVar.there (show (nb096AlphaDummy102 D R) ≠
        (nb096AlphaDummy135 D R) from (by
          unfold nb096AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0134 D R) 0)))) (show (nb096AlphaDummy104 D R q) ≠
        (nb096AlphaDummy136 D R q) from (by
          unfold nb096AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0135 D R q) 0)))) (TAlphaVar.there (show
        (nb096AlphaDummy102 D R) ≠ (nb096AlphaDummy133 D R) from (by
          unfold nb096AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0132 D R) 0)))) (show (nb096AlphaDummy104 D R q) ≠
        (nb096AlphaDummy134 D R q) from (by
          unfold nb096AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0133 D R q) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb096AlphaDummy102 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb096AlphaDummy104 D R q))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy116 D R) from
        (by
          unfold nb096AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  1)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy119 D R q) from
        (by
          unfold nb096AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy115 D R) from (by
          unfold nb096AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy118 D R q) from
        (by
          unfold nb096AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold
            nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold
            nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy116
        D R) ≠ (nb096AlphaDummy127 D R) from (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy116
        D R) ≠ (nb096AlphaDummy127 D R) from (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠ (nb096AlphaDummy129 D R) from
        (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy129 D R) from (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy113 D R) from
        (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy135 D R), (nb096AlphaDummy136 D R q)),
        ((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb096AlphaDummy133 D R), (nb096AlphaDummy134 D R q)),
                    ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
                    ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
                    ((nb096AlphaDummy131 D R), (nb096AlphaDummy132 D R q)),
                    ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
                    ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
                    ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
                    ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                    ((nb096AlphaDummy000 D R), q),
                    ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb096_split_alpha_0006`. -/
@[expose]
noncomputable def nb096SplitAlpha0006 (D : Class) (R : Class) (q : Var) :
    TAlphaWff
      [((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy105 D R)) (synCcompl
            (Class.cab (nb096AlphaDummy101 D R)
              (synWrex (nb096AlphaDummy102 D R) (Class.cv (nb096AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                  (synCphi (Class.cv (nb096AlphaDummy102 D R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy105 D R)) (synCcompl
              (Class.cab (nb096AlphaDummy101 D R) (synWrex (nb096AlphaDummy102 D R)
                  (Class.cv (nb096AlphaDummy041 D R))
                  (Wff.classEq (Class.cv (nb096AlphaDummy101 D R))
                    (synCun (synCphi (Class.cv (nb096AlphaDummy102 D R)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb096AlphaDummy106 D R q)) (synCcompl
            (Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
                (Class.cv (nb096AlphaDummy044 D R q))
                (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                  (synCphi (Class.cv (nb096AlphaDummy104 D R q)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb096AlphaDummy106 D R q)) (synCcompl
              (Class.cab (nb096AlphaDummy103 D R q) (synWrex (nb096AlphaDummy104 D R q)
                  (Class.cv (nb096AlphaDummy043 D R q))
                  (Wff.classEq (Class.cv (nb096AlphaDummy103 D R q))
                    (synCun (synCphi (Class.cv (nb096AlphaDummy104 D R q)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy102 D R) from
                            (by
                              unfold nb096AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0098 D R) 1)))) (show
                            (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy104 D R q) from
                            (by
                              unfold nb096AlphaDummy104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
                          (TAlphaVar.there (show
                              (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy101 D R) from (by
                                unfold nb096AlphaDummy101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0098 D R) 0)))) (show
                              (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy103 D R q) from
                              (by
                                unfold nb096AlphaDummy103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0100 D R q)
                                        0)))) (TAlphaVar.there (show
                                (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy107 D R) from
                                (by
                                  unfold nb096AlphaDummy107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0102 D R)
                                          0)))) (show (nb096AlphaDummy044 D R q) ≠
                                  (nb096AlphaDummy108 D R q) from (by
                                  unfold nb096AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0103 D R q)
                                          0)))) (TAlphaVar.there (show
                                  (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy105 D R) from
                                  (by
                                    unfold nb096AlphaDummy105;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0099 D R)
                                            0)))) (show (nb096AlphaDummy044 D R q) ≠
                                    (nb096AlphaDummy106 D R q) from (by
                                    unfold nb096AlphaDummy106;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0101 D R q)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
                              ((Class.cv (nb096AlphaDummy041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
                              ((Class.cv (nb096AlphaDummy043 D R q))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb096AlphaDummy102 D R) ≠ (nb096AlphaDummy109 D R)
                                    from (by
                                      unfold nb096AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0104 D R)
                                              0)))) (show (nb096AlphaDummy104 D R q) ≠
                                      (nb096AlphaDummy111 D R q) from (by
                                      unfold nb096AlphaDummy111;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0105 D R q) 0))))
                                  (TAlphaVar.there (show (nb096AlphaDummy102 D R) ≠
                                        (nb096AlphaDummy110 D R) from (by
                                        unfold nb096AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 1)))) (show
                                      (nb096AlphaDummy104 D R q) ≠
                                        (nb096AlphaDummy112 D R q) from (by
                                        unfold nb096AlphaDummy112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb096AlphaDummy102 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb096AlphaDummy104 D R q))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy116 D R) from (by
          unfold nb096AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108 D
                    R)
                  1)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy119 D R q) from
        (by
          unfold nb096AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109 D
                    R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy115 D R) from (by
          unfold nb096AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy118 D R q) from
        (by
          unfold nb096AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111
        D R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy127 D R) from
        (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy116
        D R) ≠ (nb096AlphaDummy127 D R) from (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠ (nb096AlphaDummy129 D R) from
        (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy129 D R) from (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy102 D R) from
                            (by
                              unfold nb096AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0098 D R) 1)))) (show
                            (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy104 D R q) from
                            (by
                              unfold nb096AlphaDummy104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb096_support_mem_0100 D R q) 1))))
                          (TAlphaVar.there (show
                              (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy101 D R) from (by
                                unfold nb096AlphaDummy101;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0098 D R) 0)))) (show
                              (nb096AlphaDummy044 D R q) ≠ (nb096AlphaDummy103 D R q) from
                              (by
                                unfold nb096AlphaDummy103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb096_support_mem_0100 D R q)
                                        0)))) (TAlphaVar.there (show
                                (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy107 D R) from
                                (by
                                  unfold nb096AlphaDummy107;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0102 D R)
                                          0)))) (show (nb096AlphaDummy044 D R q) ≠
                                  (nb096AlphaDummy108 D R q) from (by
                                  unfold nb096AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb096_support_mem_0103 D R q)
                                          0)))) (TAlphaVar.there (show
                                  (nb096AlphaDummy042 D R) ≠ (nb096AlphaDummy105 D R) from
                                  (by
                                    unfold nb096AlphaDummy105;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0099 D R)
                                            0)))) (show (nb096AlphaDummy044 D R q) ≠
                                    (nb096AlphaDummy106 D R q) from (by
                                    unfold nb096AlphaDummy106;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb096_support_mem_0101 D R q)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb096AlphaDummy042 D R))).fv ∪
                              ((Class.cv (nb096AlphaDummy041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb096AlphaDummy044 D R q))).fv ∪
                              ((Class.cv (nb096AlphaDummy043 D R q))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb096AlphaDummy102 D R) ≠ (nb096AlphaDummy109 D R)
                                    from (by
                                      unfold nb096AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb096_support_mem_0104 D R)
                                              0)))) (show (nb096AlphaDummy104 D R q) ≠
                                      (nb096AlphaDummy111 D R q) from (by
                                      unfold nb096AlphaDummy111;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb096_support_mem_0105 D R q) 0))))
                                  (TAlphaVar.there (show (nb096AlphaDummy102 D R) ≠
                                        (nb096AlphaDummy110 D R) from (by
                                        unfold nb096AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0104 D R) 1)))) (show
                                      (nb096AlphaDummy104 D R q) ≠
                                        (nb096AlphaDummy112 D R q) from (by
                                        unfold nb096AlphaDummy112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb096_support_mem_0105 D R q) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb096AlphaDummy102 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb096AlphaDummy104 D R q))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy116 D R) from (by
          unfold nb096AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108 D
                    R)
                  1)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy119 D R q) from
        (by
          unfold nb096AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109 D
                    R q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy115 D R) from (by
          unfold nb096AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0108
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy118 D R q) from
        (by
          unfold nb096AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0109
                    D R q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106
                    D R)
                  0)))) (show (nb096AlphaDummy111 D R q) ≠ (nb096AlphaDummy114 D R q) from
        (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107
                    D R q)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy123 D R) from
        (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0112
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0113
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0110
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0111
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy123 D R) from (by
          unfold
            nb096AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0116
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy124 D R q) from
        (by
          unfold
            nb096AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0117
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy121 D R) from (by
          unfold
            nb096AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0114
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy122 D R q) from
        (by
          unfold
            nb096AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0115
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy117 D R), (nb096AlphaDummy120 D R q)),
        ((nb096AlphaDummy116 D R), (nb096AlphaDummy119 D R q)),
        ((nb096AlphaDummy115 D R), (nb096AlphaDummy118 D R q)),
        ((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb096AlphaDummy109 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111
        D R q))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠ (nb096AlphaDummy127 D R) from
        (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy116
        D R) ≠ (nb096AlphaDummy127 D R) from (by
          unfold
            nb096AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0120
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy128 D R q) from
        (by
          unfold
            nb096AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0121
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy116 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0118
                    D
                    R)
                  0)))) (show (nb096AlphaDummy119 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0119
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy109
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy111 D R q))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠ (nb096AlphaDummy129 D R) from
        (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy117
        D R) ≠ (nb096AlphaDummy129 D R) from (by
          unfold
            nb096AlphaDummy129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0124
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy130 D R q) from
        (by
          unfold
            nb096AlphaDummy130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0125
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy117 D R) ≠
        (nb096AlphaDummy125 D R) from (by
          unfold
            nb096AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0122
                    D
                    R)
                  0)))) (show (nb096AlphaDummy120 D R q) ≠ (nb096AlphaDummy126 D R q) from
        (by
          unfold
            nb096AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0123
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb096AlphaDummy109 D R) ≠
        (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb096AlphaDummy109 D R) ≠ (nb096AlphaDummy113 D R) from (by
          unfold nb096AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0106 D R) 0)))) (show (nb096AlphaDummy111 D R q) ≠
        (nb096AlphaDummy114 D R q) from (by
          unfold nb096AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0107 D R q)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy113 D R), (nb096AlphaDummy114 D R q)),
        ((nb096AlphaDummy109 D R), (nb096AlphaDummy111 D R q)),
        ((nb096AlphaDummy110 D R), (nb096AlphaDummy112 D R q)),
        ((nb096AlphaDummy102 D R), (nb096AlphaDummy104 D R q)),
        ((nb096AlphaDummy101 D R), (nb096AlphaDummy103 D R q)),
        ((nb096AlphaDummy107 D R), (nb096AlphaDummy108 D R q)),
        ((nb096AlphaDummy105 D R), (nb096AlphaDummy106 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb096SplitAlpha0005 D R q)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb096SplitAlpha0005 D R q)))))))))))

theorem nb096_wpp_notmem_0352 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy042, fv_syn_cen] using (nb096_compact_fv_empty_0062 D R)

theorem nb096_wpp_notmem_0353 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy044, fv_syn_cen] using (nb096_compact_fv_empty_0063 D R q)

theorem nb096_wpp_notmem_0354 (D : Class) (R : Class) :
    (nb096AlphaDummy041 D R) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy041, fv_syn_cen] using (nb096_compact_fv_empty_0064 D R)

theorem nb096_wpp_notmem_0355 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy043 D R q) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy043, fv_syn_cen] using (nb096_compact_fv_empty_0065 D R q)

theorem nb096_wpp_notmem_0356 (D : Class) (R : Class) :
    (nb096AlphaDummy001 D R) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy001, fv_syn_cen] using (nb096_compact_fv_empty_0020 D R)

theorem nb096_wpp_notmem_0357 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy002 D R q) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy002, fv_syn_cen] using (nb096_compact_fv_empty_0021 D R q)

theorem nb096_wpp_notmem_0358 (D : Class) (R : Class) :
    (nb096AlphaDummy000 D R) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy000, fv_syn_cen] using (nb096_compact_fv_empty_0022 D R)

theorem nb096_wpp_notmem_0359 (q : Var) : q ∉ ((synCen)).fv := by
  simpa only [fv_syn_cen] using (nb096_compact_fv_empty_0023 q)

theorem nb096_wpp_notmem_0360 (D : Class) (R : Class) :
    (nb096AlphaDummy003 D R) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy003, fv_syn_cen] using (nb096_compact_fv_empty_0024 D R)

theorem nb096_wpp_notmem_0361 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy004 D R q) ∉ ((synCen)).fv := by
  simpa only [nb096AlphaDummy004, fv_syn_cen] using (nb096_compact_fv_empty_0025 D R q)

theorem nb096_compact_envfresh_0024 (D : Class) (R : Class) (q : Var) :
    TEnvFresh
      [((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      ((synCen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096AlphaDummy042 D R) (nb096AlphaDummy044 D R q)
      (nb096_wpp_notmem_0352 D R) (nb096_wpp_notmem_0353 D R q)
      (TEnvFresh.consFresh (nb096AlphaDummy041 D R) (nb096AlphaDummy043 D R q)
        (nb096_wpp_notmem_0354 D R) (nb096_wpp_notmem_0355 D R q)
        (TEnvFresh.consFresh (nb096AlphaDummy001 D R) (nb096AlphaDummy002 D R q)
          (nb096_wpp_notmem_0356 D R) (nb096_wpp_notmem_0357 D R q)
          (TEnvFresh.consFresh (nb096AlphaDummy000 D R) q (nb096_wpp_notmem_0358 D R)
            (nb096_wpp_notmem_0359 q)
            (TEnvFresh.consFresh (nb096AlphaDummy003 D R) (nb096AlphaDummy004 D R q)
              (nb096_wpp_notmem_0360 D R) (nb096_wpp_notmem_0361 D R q)
              (TEnvFresh.nil ((synCen)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
