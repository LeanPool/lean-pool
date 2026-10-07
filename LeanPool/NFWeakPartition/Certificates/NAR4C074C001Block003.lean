/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C074C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C074C001Part010`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0006`. -/
@[expose]
noncomputable def nb074SplitAlpha0006 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy119), (nb074AlphaDummy120 x)),
        ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
        ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
        ((nb074AlphaDummy117), (nb074AlphaDummy118 x)),
        ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
        ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy119))
          (synCcompl (synCphi (Class.cv (nb074AlphaDummy088))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy119)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy120 x))
          (synCcompl (synCphi (Class.cv (nb074AlphaDummy090 x))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy120 x))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy095) from (by
                              unfold nb074AlphaDummy095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                          (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy097 x) from (by
                              unfold nb074AlphaDummy097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                          (TAlphaVar.there
                            (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy096) from (by
                                unfold nb074AlphaDummy096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                            (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy098 x) from (by
                                unfold nb074AlphaDummy098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                            (TAlphaVar.there
                              (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy121) from (by
                                  unfold nb074AlphaDummy121;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0122) 0))))
                              (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy122 x) from
                                (by
                                  unfold nb074AlphaDummy122;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0123 x) 0))))
                              (TAlphaVar.there
                                (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy119) from (by
                                    unfold nb074AlphaDummy119;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0120) 0)))) (show
                                  (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy120 x) from (by
                                    unfold nb074AlphaDummy120;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0121 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074AlphaDummy088))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074AlphaDummy090 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy095) ≠ (nb074AlphaDummy102) from (by
          unfold nb074AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy105 x) from (by
          unfold nb074AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy101) from (by
          unfold nb074AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy104 x) from (by
          unfold nb074AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
          unfold nb074AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094) 0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy100 x) from (by
          unfold nb074AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy121), (nb074AlphaDummy122 x)), ((nb074AlphaDummy119),
        (nb074AlphaDummy120 x)), ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
        ((nb074AlphaDummy087), (nb074AlphaDummy089 x)), ((nb074AlphaDummy117),
        (nb074AlphaDummy118 x)), ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy121), (nb074AlphaDummy122 x)), ((nb074AlphaDummy119),
        (nb074AlphaDummy120 x)), ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
        ((nb074AlphaDummy087), (nb074AlphaDummy089 x)), ((nb074AlphaDummy117),
        (nb074AlphaDummy118 x)), ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy097 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠
        (nb074AlphaDummy113) from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy113)
        from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠
        (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
                                        unfold nb074AlphaDummy099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074AlphaDummy097 x) ≠
                                        (nb074AlphaDummy100 x) from (by
                                        unfold nb074AlphaDummy100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                    ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                    ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                    ((nb074AlphaDummy121), (nb074AlphaDummy122 x)),
                                    ((nb074AlphaDummy119), (nb074AlphaDummy120 x)),
                                    ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                    ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                    ((nb074AlphaDummy117), (nb074AlphaDummy118 x)),
                                    ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from
                                    (by
                                      unfold nb074AlphaDummy099;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0094)
                                              0)))) (show
                                    (nb074AlphaDummy097 x) ≠ (nb074AlphaDummy100 x) from
                                    (by
                                      unfold nb074AlphaDummy100;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0095 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
                                        unfold nb074AlphaDummy099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074AlphaDummy097 x) ≠
                                        (nb074AlphaDummy100 x) from (by
                                        unfold nb074AlphaDummy100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                    ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                    ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                    ((nb074AlphaDummy121), (nb074AlphaDummy122 x)),
                                    ((nb074AlphaDummy119), (nb074AlphaDummy120 x)),
                                    ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                    ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                    ((nb074AlphaDummy117), (nb074AlphaDummy118 x)),
                                    ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy095) from (by
                              unfold nb074AlphaDummy095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                          (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy097 x) from (by
                              unfold nb074AlphaDummy097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                          (TAlphaVar.there
                            (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy096) from (by
                                unfold nb074AlphaDummy096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                            (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy098 x) from (by
                                unfold nb074AlphaDummy098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                            (TAlphaVar.there
                              (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy121) from (by
                                  unfold nb074AlphaDummy121;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0122) 0))))
                              (show (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy122 x) from
                                (by
                                  unfold nb074AlphaDummy122;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0123 x) 0))))
                              (TAlphaVar.there
                                (show (nb074AlphaDummy088) ≠ (nb074AlphaDummy119) from (by
                                    unfold nb074AlphaDummy119;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0120) 0)))) (show
                                  (nb074AlphaDummy090 x) ≠ (nb074AlphaDummy120 x) from (by
                                    unfold nb074AlphaDummy120;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0121 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074AlphaDummy088))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074AlphaDummy090 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy095) ≠ (nb074AlphaDummy102) from (by
          unfold nb074AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy105 x) from (by
          unfold nb074AlphaDummy105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy101) from (by
          unfold nb074AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy104 x) from (by
          unfold nb074AlphaDummy104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
          unfold nb074AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094) 0)))) (show (nb074AlphaDummy097 x) ≠
        (nb074AlphaDummy100 x) from (by
          unfold nb074AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy121), (nb074AlphaDummy122 x)), ((nb074AlphaDummy119),
        (nb074AlphaDummy120 x)), ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
        ((nb074AlphaDummy087), (nb074AlphaDummy089 x)), ((nb074AlphaDummy117),
        (nb074AlphaDummy118 x)), ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy109) from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy109)
        from (by
          unfold
            nb074AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy110 x) from (by
          unfold
            nb074AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy107)
        from (by
          unfold
            nb074AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy108 x) from (by
          unfold
            nb074AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy103), (nb074AlphaDummy106 x)), ((nb074AlphaDummy102),
        (nb074AlphaDummy105 x)), ((nb074AlphaDummy101), (nb074AlphaDummy104 x)),
        ((nb074AlphaDummy099), (nb074AlphaDummy100 x)), ((nb074AlphaDummy095),
        (nb074AlphaDummy097 x)), ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
        ((nb074AlphaDummy121), (nb074AlphaDummy122 x)), ((nb074AlphaDummy119),
        (nb074AlphaDummy120 x)), ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
        ((nb074AlphaDummy087), (nb074AlphaDummy089 x)), ((nb074AlphaDummy117),
        (nb074AlphaDummy118 x)), ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy097 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠
        (nb074AlphaDummy113) from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy113)
        from (by
          unfold
            nb074AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy114 x) from (by
          unfold
            nb074AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy102) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074AlphaDummy105 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy095))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy097 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy103) ≠
        (nb074AlphaDummy115) from (by
          unfold
            nb074AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy116 x) from (by
          unfold
            nb074AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy103) ≠ (nb074AlphaDummy111)
        from (by
          unfold
            nb074AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074AlphaDummy106 x) ≠ (nb074AlphaDummy112 x) from (by
          unfold
            nb074AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
                                        unfold nb074AlphaDummy099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074AlphaDummy097 x) ≠
                                        (nb074AlphaDummy100 x) from (by
                                        unfold nb074AlphaDummy100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                    ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                    ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                    ((nb074AlphaDummy121), (nb074AlphaDummy122 x)),
                                    ((nb074AlphaDummy119), (nb074AlphaDummy120 x)),
                                    ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                    ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                    ((nb074AlphaDummy117), (nb074AlphaDummy118 x)),
                                    ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from
                                    (by
                                      unfold nb074AlphaDummy099;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0094)
                                              0)))) (show
                                    (nb074AlphaDummy097 x) ≠ (nb074AlphaDummy100 x) from
                                    (by
                                      unfold nb074AlphaDummy100;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0095 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy095) ≠ (nb074AlphaDummy099) from (by
                                        unfold nb074AlphaDummy099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074AlphaDummy097 x) ≠
                                        (nb074AlphaDummy100 x) from (by
                                        unfold nb074AlphaDummy100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy099), (nb074AlphaDummy100 x)),
                                    ((nb074AlphaDummy095), (nb074AlphaDummy097 x)),
                                    ((nb074AlphaDummy096), (nb074AlphaDummy098 x)),
                                    ((nb074AlphaDummy121), (nb074AlphaDummy122 x)),
                                    ((nb074AlphaDummy119), (nb074AlphaDummy120 x)),
                                    ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
                                    ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
                                    ((nb074AlphaDummy117), (nb074AlphaDummy118 x)),
                                    ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb074AlphaDummy119), (nb074AlphaDummy120 x)),
            ((nb074AlphaDummy088), (nb074AlphaDummy090 x)),
            ((nb074AlphaDummy087), (nb074AlphaDummy089 x)),
            ((nb074AlphaDummy117), (nb074AlphaDummy118 x)),
            ((nb074AlphaDummy091), (nb074AlphaDummy092 x)),
            ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
            ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
            ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
            ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
            ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
            ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
            ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part011`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0007`. -/
@[expose]
noncomputable def nb074SplitAlpha0007 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
        ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
        ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy129))
          (Class.cab (nb074AlphaDummy123)
            (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
              (Wff.classEq (Class.cv (nb074AlphaDummy123))
                (synCphi (Class.cv (nb074AlphaDummy124))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy129)) (Class.cab (nb074AlphaDummy123)
              (synWrex (nb074AlphaDummy124) (Class.cv (nb074AlphaDummy082))
                (Wff.classEq (Class.cv (nb074AlphaDummy123))
                  (synCphi (Class.cv (nb074AlphaDummy124)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy130 x))
          (Class.cab (nb074AlphaDummy125 x)
            (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
              (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                (synCphi (Class.cv (nb074AlphaDummy126 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy130 x))
            (Class.cab (nb074AlphaDummy125 x)
              (synWrex (nb074AlphaDummy126 x) (Class.cv (nb074AlphaDummy084 x))
                (Wff.classEq (Class.cv (nb074AlphaDummy125 x))
                  (synCphi (Class.cv (nb074AlphaDummy126 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy124) from
                    (by
                      unfold nb074AlphaDummy124;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
                  (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy126 x) from (by
                      unfold nb074AlphaDummy126;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))))
                  (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy123) from
                      (by
                        unfold nb074AlphaDummy123;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))))
                    (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy125 x) from (by
                        unfold nb074AlphaDummy125;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0126 x) 0)))) (TAlphaVar.there
                      (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy129) from (by
                          unfold nb074AlphaDummy129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0128) 0))))
                      (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy130 x) from (by
                          unfold nb074AlphaDummy130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0129 x) 0))))
                      (TAlphaVar.there
                        (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy127) from (by
                            unfold nb074AlphaDummy127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0125) 0))))
                        (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy128 x) from (by
                            unfold nb074AlphaDummy128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0127 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy082))).fv ∪
                      ((Class.cv (nb074AlphaDummy081))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb074AlphaDummy084 x))).fv ∪
                      ((Class.cv (nb074AlphaDummy083 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy131) from (by
                              unfold nb074AlphaDummy131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0130) 0))))
                          (show (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy133 x) from (by
                              unfold nb074AlphaDummy133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0131 x) 0))))
                          (TAlphaVar.there
                            (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy132) from (by
                                unfold nb074AlphaDummy132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0130) 1))))
                            (show (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy134 x) from (by
                                unfold nb074AlphaDummy134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0131 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074AlphaDummy124))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074AlphaDummy126 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy131) ≠ (nb074AlphaDummy138) from (by
          unfold nb074AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 1)))) (show (nb074AlphaDummy133 x) ≠
        (nb074AlphaDummy141 x) from (by
          unfold nb074AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy131) ≠ (nb074AlphaDummy137) from (by
          unfold nb074AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 0)))) (show (nb074AlphaDummy133 x) ≠
        (nb074AlphaDummy140 x) from (by
          unfold nb074AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy131) ≠ (nb074AlphaDummy135) from (by
          unfold nb074AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0132) 0)))) (show (nb074AlphaDummy133 x) ≠
        (nb074AlphaDummy136 x) from (by
          unfold nb074AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0133 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy139), (nb074AlphaDummy142 x)), ((nb074AlphaDummy138),
        (nb074AlphaDummy141 x)), ((nb074AlphaDummy137), (nb074AlphaDummy140 x)),
        ((nb074AlphaDummy135), (nb074AlphaDummy136 x)), ((nb074AlphaDummy131),
        (nb074AlphaDummy133 x)), ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
        ((nb074AlphaDummy124), (nb074AlphaDummy126 x)), ((nb074AlphaDummy123),
        (nb074AlphaDummy125 x)), ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
        ((nb074AlphaDummy127), (nb074AlphaDummy128 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy145) from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy145)
        from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy145) from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy145)
        from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy139), (nb074AlphaDummy142 x)), ((nb074AlphaDummy138),
        (nb074AlphaDummy141 x)), ((nb074AlphaDummy137), (nb074AlphaDummy140 x)),
        ((nb074AlphaDummy135), (nb074AlphaDummy136 x)), ((nb074AlphaDummy131),
        (nb074AlphaDummy133 x)), ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
        ((nb074AlphaDummy124), (nb074AlphaDummy126 x)), ((nb074AlphaDummy123),
        (nb074AlphaDummy125 x)), ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
        ((nb074AlphaDummy127), (nb074AlphaDummy128 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy131))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy133 x))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy138) ≠
        (nb074AlphaDummy149) from (by
          unfold
            nb074AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy150 x) from (by
          unfold
            nb074AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy149)
        from (by
          unfold
            nb074AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy150 x) from (by
          unfold
            nb074AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy151) from (by
          unfold
            nb074AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy152 x) from (by
          unfold
            nb074AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy139) ≠
        (nb074AlphaDummy151) from (by
          unfold
            nb074AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy152 x) from (by
          unfold
            nb074AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy131) ≠ (nb074AlphaDummy135) from (by
                                        unfold nb074AlphaDummy135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074AlphaDummy133 x) ≠
                                        (nb074AlphaDummy136 x) from (by
                                        unfold nb074AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy135), (nb074AlphaDummy136 x)),
                                    ((nb074AlphaDummy131), (nb074AlphaDummy133 x)),
                                    ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
                                    ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                    ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                    ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
                                    ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074AlphaDummy131) ≠ (nb074AlphaDummy135) from
                                    (by
                                      unfold nb074AlphaDummy135;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0132)
                                              0)))) (show
                                    (nb074AlphaDummy133 x) ≠ (nb074AlphaDummy136 x) from
                                    (by
                                      unfold nb074AlphaDummy136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0133 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy131) ≠ (nb074AlphaDummy135) from (by
                                        unfold nb074AlphaDummy135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074AlphaDummy133 x) ≠
                                        (nb074AlphaDummy136 x) from (by
                                        unfold nb074AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb074AlphaDummy135), (nb074AlphaDummy136 x)),
                                    ((nb074AlphaDummy131), (nb074AlphaDummy133 x)),
                                    ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
                                    ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                    ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                    ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
                                    ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
                                    ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                    ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                    ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                    ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                    ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                    ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                    ((nb074AlphaDummy000), x),
                                    ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy124) from
                      (by
                        unfold nb074AlphaDummy124;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
                    (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy126 x) from (by
                        unfold nb074AlphaDummy126;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0126 x) 1)))) (TAlphaVar.there
                      (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy123) from (by
                          unfold nb074AlphaDummy123;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0124) 0))))
                      (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy125 x) from (by
                          unfold nb074AlphaDummy125;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0126 x) 0))))
                      (TAlphaVar.there
                        (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy129) from (by
                            unfold nb074AlphaDummy129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0128) 0))))
                        (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy130 x) from (by
                            unfold nb074AlphaDummy130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0129 x) 0))))
                        (TAlphaVar.there
                          (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy127) from (by
                              unfold nb074AlphaDummy127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0125) 0))))
                          (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy128 x) from (by
                              unfold nb074AlphaDummy128;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0127 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb074AlphaDummy082))).fv ∪
                        ((Class.cv (nb074AlphaDummy081))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb074AlphaDummy084 x))).fv ∪
                        ((Class.cv (nb074AlphaDummy083 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy131) from (by
                                unfold nb074AlphaDummy131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0130) 0))))
                            (show (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy133 x) from (by
                                unfold nb074AlphaDummy133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0131 x) 0))))
                            (TAlphaVar.there
                              (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy132) from (by
                                  unfold nb074AlphaDummy132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0130) 1))))
                              (show (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy134 x) from
                                (by
                                  unfold nb074AlphaDummy134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0131 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb074AlphaDummy124))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb074AlphaDummy126 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy131) ≠ (nb074AlphaDummy138) from (by
          unfold nb074AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 1)))) (show (nb074AlphaDummy133 x) ≠
        (nb074AlphaDummy141 x) from (by
          unfold nb074AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy131) ≠ (nb074AlphaDummy137) from (by
          unfold nb074AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 0)))) (show (nb074AlphaDummy133 x) ≠
        (nb074AlphaDummy140 x) from (by
          unfold nb074AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy131) ≠ (nb074AlphaDummy135)
        from (by
          unfold nb074AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0132)
                  0)))) (show (nb074AlphaDummy133 x) ≠ (nb074AlphaDummy136 x) from (by
          unfold nb074AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0133 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy139), (nb074AlphaDummy142 x)), ((nb074AlphaDummy138),
        (nb074AlphaDummy141 x)), ((nb074AlphaDummy137), (nb074AlphaDummy140 x)),
        ((nb074AlphaDummy135), (nb074AlphaDummy136 x)), ((nb074AlphaDummy131),
        (nb074AlphaDummy133 x)), ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
        ((nb074AlphaDummy124), (nb074AlphaDummy126 x)), ((nb074AlphaDummy123),
        (nb074AlphaDummy125 x)), ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
        ((nb074AlphaDummy127), (nb074AlphaDummy128 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy145) from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy145)
        from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy145) from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy145)
        from (by
          unfold
            nb074AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy146 x) from (by
          unfold
            nb074AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy143)
        from (by
          unfold
            nb074AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy144 x) from (by
          unfold
            nb074AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb074AlphaDummy139), (nb074AlphaDummy142 x)), ((nb074AlphaDummy138),
        (nb074AlphaDummy141 x)), ((nb074AlphaDummy137), (nb074AlphaDummy140 x)),
        ((nb074AlphaDummy135), (nb074AlphaDummy136 x)), ((nb074AlphaDummy131),
        (nb074AlphaDummy133 x)), ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
        ((nb074AlphaDummy124), (nb074AlphaDummy126 x)), ((nb074AlphaDummy123),
        (nb074AlphaDummy125 x)), ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
        ((nb074AlphaDummy127), (nb074AlphaDummy128 x)), ((nb074AlphaDummy082),
        (nb074AlphaDummy084 x)), ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)), ((nb074AlphaDummy042),
        (nb074AlphaDummy044 x)), ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy131))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074AlphaDummy133
        x))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy138) ≠
        (nb074AlphaDummy149) from (by
          unfold
            nb074AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy150 x) from (by
          unfold
            nb074AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy149)
        from (by
          unfold
            nb074AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy150 x) from (by
          unfold
            nb074AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy138) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074AlphaDummy141 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy131))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074AlphaDummy133 x))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy151) from (by
          unfold
            nb074AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy152 x) from (by
          unfold
            nb074AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy139) ≠
        (nb074AlphaDummy151) from (by
          unfold
            nb074AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy152 x) from (by
          unfold
            nb074AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy139) ≠ (nb074AlphaDummy147)
        from (by
          unfold
            nb074AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074AlphaDummy142 x) ≠ (nb074AlphaDummy148 x) from (by
          unfold
            nb074AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074AlphaDummy131) ≠ (nb074AlphaDummy135) from
                                        (by
                                          unfold nb074AlphaDummy135;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0132)
                                                  0)))) (show (nb074AlphaDummy133 x) ≠
        (nb074AlphaDummy136 x) from (by
                                          unfold nb074AlphaDummy136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0133 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb074AlphaDummy135), (nb074AlphaDummy136 x)),
                                      ((nb074AlphaDummy131), (nb074AlphaDummy133 x)),
                                      ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
                                      ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                      ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                      ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
                                      ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
                                      ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                      ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                      ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                      ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                      ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                      ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                      ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
                                        (nb074AlphaDummy004 x))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074AlphaDummy131) ≠ (nb074AlphaDummy135) from (by
                                        unfold nb074AlphaDummy135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074AlphaDummy133 x) ≠
                                        (nb074AlphaDummy136 x) from (by
                                        unfold nb074AlphaDummy136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074AlphaDummy131) ≠ (nb074AlphaDummy135) from
                                        (by
                                          unfold nb074AlphaDummy135;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0132)
                                                  0)))) (show (nb074AlphaDummy133 x) ≠
        (nb074AlphaDummy136 x) from (by
                                          unfold nb074AlphaDummy136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0133 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb074AlphaDummy135), (nb074AlphaDummy136 x)),
                                      ((nb074AlphaDummy131), (nb074AlphaDummy133 x)),
                                      ((nb074AlphaDummy132), (nb074AlphaDummy134 x)),
                                      ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                      ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                      ((nb074AlphaDummy129), (nb074AlphaDummy130 x)),
                                      ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
                                      ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
                                      ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
                                      ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
                                      ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                                      ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                                      ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                                      ((nb074AlphaDummy000), x), ((nb074AlphaDummy003),
                                        (nb074AlphaDummy004 x))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
