/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block016

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part054`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0023`. -/
@[expose]
noncomputable def nb078SplitAlpha0023 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy101))
          (Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy101)) (Class.cab (nb078AlphaDummy095)
              (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
                (Wff.classEq (Class.cv (nb078AlphaDummy095))
                  (synCphi (Class.cv (nb078AlphaDummy096)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy102 f))
          (Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy102 f))
            (Class.cab (nb078AlphaDummy097 f)
              (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                  (synCphi (Class.cv (nb078AlphaDummy098 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy096) from
                    (by
                      unfold nb078AlphaDummy096;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
                  (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy098 f) from (by
                      unfold nb078AlphaDummy098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy095) from
                      (by
                        unfold nb078AlphaDummy095;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))))
                    (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy097 f) from (by
                        unfold nb078AlphaDummy097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy101) from (by
                          unfold nb078AlphaDummy101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0088) 0))))
                      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy102 f) from (by
                          unfold nb078AlphaDummy102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0089 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy099) from (by
                            unfold nb078AlphaDummy099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0085) 0))))
                        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy100 f) from (by
                            unfold nb078AlphaDummy100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0087 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
                      ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy091 f))).fv ∪
                      ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from (by
                              unfold nb078AlphaDummy103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                          (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                              unfold nb078AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from (by
                                unfold nb078AlphaDummy104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                            (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from (by
                                unfold nb078AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy098 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from (by
          unfold nb078AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy113 f) from (by
          unfold nb078AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy109) from (by
          unfold nb078AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
          unfold nb078AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy105
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                    (by
                                      unfold nb078AlphaDummy107;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0092)
                                              0)))) (show
                                    (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from
                                    (by
                                      unfold nb078AlphaDummy108;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy096) from
                      (by
                        unfold nb078AlphaDummy096;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
                    (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy098 f) from (by
                        unfold nb078AlphaDummy098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy095) from (by
                          unfold nb078AlphaDummy095;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0084) 0))))
                      (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy097 f) from (by
                          unfold nb078AlphaDummy097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0086 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy101) from (by
                            unfold nb078AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0088) 0))))
                        (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy102 f) from (by
                            unfold nb078AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0089 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy099) from (by
                              unfold nb078AlphaDummy099;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0085) 0))))
                          (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy100 f) from (by
                              unfold nb078AlphaDummy100;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0087 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy089))).fv ∪
                        ((Class.cv (nb078AlphaDummy090))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy091 f))).fv ∪
                        ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from (by
                                unfold nb078AlphaDummy103;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                            (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                                unfold nb078AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from (by
                                  unfold nb078AlphaDummy104;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                              (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from
                                (by
                                  unfold nb078AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy098 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from (by
          unfold nb078AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy113 f) from (by
          unfold nb078AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy109) from (by
          unfold nb078AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
          unfold nb078AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107)
        from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092)
                  0)))) (show (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)), ((nb078AlphaDummy095),
        (nb078AlphaDummy097 f)), ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy105
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                        (by
                                          unfold nb078AlphaDummy107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0092)
                                                  0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
                                          unfold nb078AlphaDummy108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                      ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                      ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                      ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                      ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                      ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                      ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                      ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                      ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                      ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                      ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                      ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                        (by
                                          unfold nb078AlphaDummy107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0092)
                                                  0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
                                          unfold nb078AlphaDummy108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                      ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                      ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                      ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                      ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                      ((nb078AlphaDummy101), (nb078AlphaDummy102 f)),
                                      ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                      ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                      ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                      ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                      ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                      ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part055`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0024`. -/
@[expose]
noncomputable def nb078SplitAlpha0024 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
        ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
        ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy127))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy096))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy127)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy128 f))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy098 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy128 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from (by
                              unfold nb078AlphaDummy103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                          (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                              unfold nb078AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from (by
                                unfold nb078AlphaDummy104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                            (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from (by
                                unfold nb078AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy129) from (by
                                  unfold nb078AlphaDummy129;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0120) 0))))
                              (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy130 f) from
                                (by
                                  unfold nb078AlphaDummy130;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0121 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy127) from (by
                                    unfold nb078AlphaDummy127;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0118) 0)))) (show
                                  (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy128 f) from (by
                                    unfold nb078AlphaDummy128;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0119 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy098 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from (by
          unfold nb078AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy113 f) from (by
          unfold nb078AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy109) from (by
          unfold nb078AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
          unfold nb078AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy129), (nb078AlphaDummy130 f)), ((nb078AlphaDummy127),
        (nb078AlphaDummy128 f)), ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)), ((nb078AlphaDummy125),
        (nb078AlphaDummy126 f)), ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy129), (nb078AlphaDummy130 f)), ((nb078AlphaDummy127),
        (nb078AlphaDummy128 f)), ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)), ((nb078AlphaDummy125),
        (nb078AlphaDummy126 f)), ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy105
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                                    ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                    (by
                                      unfold nb078AlphaDummy107;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0092)
                                              0)))) (show
                                    (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from
                                    (by
                                      unfold nb078AlphaDummy108;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                                    ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy103) from (by
                              unfold nb078AlphaDummy103;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0090) 0))))
                          (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy105 f) from (by
                              unfold nb078AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0091 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy104) from (by
                                unfold nb078AlphaDummy104;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0090) 1))))
                            (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy106 f) from (by
                                unfold nb078AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0091 f) 1))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy129) from (by
                                  unfold nb078AlphaDummy129;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0120) 0))))
                              (show (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy130 f) from
                                (by
                                  unfold nb078AlphaDummy130;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0121 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy096) ≠ (nb078AlphaDummy127) from (by
                                    unfold nb078AlphaDummy127;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0118) 0)))) (show
                                  (nb078AlphaDummy098 f) ≠ (nb078AlphaDummy128 f) from (by
                                    unfold nb078AlphaDummy128;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0119 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy098 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy110) from (by
          unfold nb078AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 1)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy113 f) from (by
          unfold nb078AlphaDummy113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy109) from (by
          unfold nb078AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0094) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy112 f) from (by
          unfold nb078AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
          unfold nb078AlphaDummy107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0092) 0)))) (show (nb078AlphaDummy105 f) ≠
        (nb078AlphaDummy108 f) from (by
          unfold nb078AlphaDummy108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy129), (nb078AlphaDummy130 f)), ((nb078AlphaDummy127),
        (nb078AlphaDummy128 f)), ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)), ((nb078AlphaDummy125),
        (nb078AlphaDummy126 f)), ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy117) from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0098)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0096)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy117)
        from (by
          unfold
            nb078AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0102)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy118 f) from (by
          unfold
            nb078AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy115)
        from (by
          unfold
            nb078AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0100)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy116 f) from (by
          unfold
            nb078AlphaDummy116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy111), (nb078AlphaDummy114 f)), ((nb078AlphaDummy110),
        (nb078AlphaDummy113 f)), ((nb078AlphaDummy109), (nb078AlphaDummy112 f)),
        ((nb078AlphaDummy107), (nb078AlphaDummy108 f)), ((nb078AlphaDummy103),
        (nb078AlphaDummy105 f)), ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
        ((nb078AlphaDummy129), (nb078AlphaDummy130 f)), ((nb078AlphaDummy127),
        (nb078AlphaDummy128 f)), ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
        ((nb078AlphaDummy095), (nb078AlphaDummy097 f)), ((nb078AlphaDummy125),
        (nb078AlphaDummy126 f)), ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy103))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy105
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121) from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy121)
        from (by
          unfold
            nb078AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0106)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy122 f) from (by
          unfold
            nb078AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy110) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0104)
                  0)))) (show (nb078AlphaDummy113 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy103))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy105 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy111) ≠
        (nb078AlphaDummy123) from (by
          unfold
            nb078AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0110)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy124 f) from (by
          unfold
            nb078AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy111) ≠ (nb078AlphaDummy119)
        from (by
          unfold
            nb078AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0108)
                  0)))) (show (nb078AlphaDummy114 f) ≠ (nb078AlphaDummy120 f) from (by
          unfold
            nb078AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                                    ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from
                                    (by
                                      unfold nb078AlphaDummy107;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0092)
                                              0)))) (show
                                    (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy108 f) from
                                    (by
                                      unfold nb078AlphaDummy108;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy103) ≠ (nb078AlphaDummy107) from (by
                                        unfold nb078AlphaDummy107;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0092)
                                                0)))) (show (nb078AlphaDummy105 f) ≠
                                        (nb078AlphaDummy108 f) from (by
                                        unfold nb078AlphaDummy108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy107), (nb078AlphaDummy108 f)),
                                    ((nb078AlphaDummy103), (nb078AlphaDummy105 f)),
                                    ((nb078AlphaDummy104), (nb078AlphaDummy106 f)),
                                    ((nb078AlphaDummy129), (nb078AlphaDummy130 f)),
                                    ((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
                                    ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
                                    ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
                                    ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
                                    ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy127), (nb078AlphaDummy128 f)),
            ((nb078AlphaDummy096), (nb078AlphaDummy098 f)),
            ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
            ((nb078AlphaDummy125), (nb078AlphaDummy126 f)),
            ((nb078AlphaDummy099), (nb078AlphaDummy100 f)),
            ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
            ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
            ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
            ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
            ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part056`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0025`. -/
@[expose]
noncomputable def nb078SplitAlpha0025 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy137))
          (Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy137)) (Class.cab (nb078AlphaDummy131)
              (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
                (Wff.classEq (Class.cv (nb078AlphaDummy131))
                  (synCphi (Class.cv (nb078AlphaDummy132)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy138 f))
          (Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy138 f))
            (Class.cab (nb078AlphaDummy133 f)
              (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                  (synCphi (Class.cv (nb078AlphaDummy134 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy132) from
                    (by
                      unfold nb078AlphaDummy132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
                  (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy134 f) from (by
                      unfold nb078AlphaDummy134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy131) from
                      (by
                        unfold nb078AlphaDummy131;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))))
                    (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy133 f) from (by
                        unfold nb078AlphaDummy133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0124 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy137) from (by
                          unfold nb078AlphaDummy137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0126) 0))))
                      (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy138 f) from (by
                          unfold nb078AlphaDummy138;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0127 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy135) from (by
                            unfold nb078AlphaDummy135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0123) 0))))
                        (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy136 f) from (by
                            unfold nb078AlphaDummy136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0125 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy090))).fv ∪
                      ((Class.cv (nb078AlphaDummy089))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy092 f))).fv ∪
                      ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy139) from (by
                              unfold nb078AlphaDummy139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                          (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy141 f) from (by
                              unfold nb078AlphaDummy141;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0129 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy140) from (by
                                unfold nb078AlphaDummy140;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0128) 1))))
                            (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy142 f) from (by
                                unfold nb078AlphaDummy142;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0129 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy132))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy134 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy146) from (by
          unfold nb078AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 1)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy149 f) from (by
          unfold nb078AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy139) ≠ (nb078AlphaDummy145) from (by
          unfold nb078AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 0)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy148 f) from (by
          unfold nb078AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
          unfold nb078AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0130) 0)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy144 f) from (by
          unfold nb078AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy147), (nb078AlphaDummy150 f)), ((nb078AlphaDummy146),
        (nb078AlphaDummy149 f)), ((nb078AlphaDummy145), (nb078AlphaDummy148 f)),
        ((nb078AlphaDummy143), (nb078AlphaDummy144 f)), ((nb078AlphaDummy139),
        (nb078AlphaDummy141 f)), ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
        ((nb078AlphaDummy132), (nb078AlphaDummy134 f)), ((nb078AlphaDummy131),
        (nb078AlphaDummy133 f)), ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy153) from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy153)
        from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy153) from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy153)
        from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy147), (nb078AlphaDummy150 f)), ((nb078AlphaDummy146),
        (nb078AlphaDummy149 f)), ((nb078AlphaDummy145), (nb078AlphaDummy148 f)),
        ((nb078AlphaDummy143), (nb078AlphaDummy144 f)), ((nb078AlphaDummy139),
        (nb078AlphaDummy141 f)), ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
        ((nb078AlphaDummy132), (nb078AlphaDummy134 f)), ((nb078AlphaDummy131),
        (nb078AlphaDummy133 f)), ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy139))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy141
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy157) from (by
          unfold
            nb078AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy158 f) from (by
          unfold
            nb078AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy157)
        from (by
          unfold
            nb078AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy158 f) from (by
          unfold
            nb078AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy159) from (by
          unfold
            nb078AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy160 f) from (by
          unfold
            nb078AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy147) ≠
        (nb078AlphaDummy159) from (by
          unfold
            nb078AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy160 f) from (by
          unfold
            nb078AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                        unfold nb078AlphaDummy143;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0130)
                                                0)))) (show (nb078AlphaDummy141 f) ≠
                                        (nb078AlphaDummy144 f) from (by
                                        unfold nb078AlphaDummy144;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy143), (nb078AlphaDummy144 f)),
                                    ((nb078AlphaDummy139), (nb078AlphaDummy141 f)),
                                    ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
                                    ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                    ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                    ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
                                    ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from
                                    (by
                                      unfold nb078AlphaDummy143;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0130)
                                              0)))) (show
                                    (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from
                                    (by
                                      unfold nb078AlphaDummy144;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0131 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                        unfold nb078AlphaDummy143;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0130)
                                                0)))) (show (nb078AlphaDummy141 f) ≠
                                        (nb078AlphaDummy144 f) from (by
                                        unfold nb078AlphaDummy144;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy143), (nb078AlphaDummy144 f)),
                                    ((nb078AlphaDummy139), (nb078AlphaDummy141 f)),
                                    ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
                                    ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                    ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                    ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
                                    ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy132) from
                      (by
                        unfold nb078AlphaDummy132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
                    (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy134 f) from (by
                        unfold nb078AlphaDummy134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0124 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy131) from (by
                          unfold nb078AlphaDummy131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0122) 0))))
                      (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy133 f) from (by
                          unfold nb078AlphaDummy133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0124 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy137) from (by
                            unfold nb078AlphaDummy137;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0126) 0))))
                        (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy138 f) from (by
                            unfold nb078AlphaDummy138;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0127 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy135) from (by
                              unfold nb078AlphaDummy135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0123) 0))))
                          (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy136 f) from (by
                              unfold nb078AlphaDummy136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0125 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy090))).fv ∪
                        ((Class.cv (nb078AlphaDummy089))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy092 f))).fv ∪
                        ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy139) from (by
                                unfold nb078AlphaDummy139;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                            (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy141 f) from (by
                                unfold nb078AlphaDummy141;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0129 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy140) from (by
                                  unfold nb078AlphaDummy140;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0128) 1))))
                              (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy142 f) from
                                (by
                                  unfold nb078AlphaDummy142;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0129 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy132))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy134 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy139) ≠ (nb078AlphaDummy146) from (by
          unfold nb078AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 1)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy149 f) from (by
          unfold nb078AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy139) ≠ (nb078AlphaDummy145) from (by
          unfold nb078AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 0)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy148 f) from (by
          unfold nb078AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143)
        from (by
          unfold nb078AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0130)
                  0)))) (show (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from (by
          unfold nb078AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy147), (nb078AlphaDummy150 f)), ((nb078AlphaDummy146),
        (nb078AlphaDummy149 f)), ((nb078AlphaDummy145), (nb078AlphaDummy148 f)),
        ((nb078AlphaDummy143), (nb078AlphaDummy144 f)), ((nb078AlphaDummy139),
        (nb078AlphaDummy141 f)), ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
        ((nb078AlphaDummy132), (nb078AlphaDummy134 f)), ((nb078AlphaDummy131),
        (nb078AlphaDummy133 f)), ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy153) from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy153)
        from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy153) from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy153)
        from (by
          unfold
            nb078AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy154 f) from (by
          unfold
            nb078AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy151)
        from (by
          unfold
            nb078AlphaDummy151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy152 f) from (by
          unfold
            nb078AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy147), (nb078AlphaDummy150 f)), ((nb078AlphaDummy146),
        (nb078AlphaDummy149 f)), ((nb078AlphaDummy145), (nb078AlphaDummy148 f)),
        ((nb078AlphaDummy143), (nb078AlphaDummy144 f)), ((nb078AlphaDummy139),
        (nb078AlphaDummy141 f)), ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
        ((nb078AlphaDummy132), (nb078AlphaDummy134 f)), ((nb078AlphaDummy131),
        (nb078AlphaDummy133 f)), ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy204),
        (nb078AlphaDummy206 f)), ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy139))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy141
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy157) from (by
          unfold
            nb078AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy158 f) from (by
          unfold
            nb078AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy157)
        from (by
          unfold
            nb078AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy158 f) from (by
          unfold
            nb078AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy146) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078AlphaDummy149 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy159) from (by
          unfold
            nb078AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy160 f) from (by
          unfold
            nb078AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy147) ≠
        (nb078AlphaDummy159) from (by
          unfold
            nb078AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy160 f) from (by
          unfold
            nb078AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy147) ≠ (nb078AlphaDummy155)
        from (by
          unfold
            nb078AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078AlphaDummy150 f) ≠ (nb078AlphaDummy156 f) from (by
          unfold
            nb078AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from
                                        (by
                                          unfold nb078AlphaDummy143;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0130)
                                                  0)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy144 f) from (by
                                          unfold nb078AlphaDummy144;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy143), (nb078AlphaDummy144 f)),
                                      ((nb078AlphaDummy139), (nb078AlphaDummy141 f)),
                                      ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
                                      ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                      ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                      ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
                                      ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
                                      ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                      ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                      ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                      ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                      ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                        unfold nb078AlphaDummy143;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0130)
                                                0)))) (show (nb078AlphaDummy141 f) ≠
                                        (nb078AlphaDummy144 f) from (by
                                        unfold nb078AlphaDummy144;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from
                                        (by
                                          unfold nb078AlphaDummy143;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0130)
                                                  0)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy144 f) from (by
                                          unfold nb078AlphaDummy144;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy143), (nb078AlphaDummy144 f)),
                                      ((nb078AlphaDummy139), (nb078AlphaDummy141 f)),
                                      ((nb078AlphaDummy140), (nb078AlphaDummy142 f)),
                                      ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                      ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                      ((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
                                      ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
                                      ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                      ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                      ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                      ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                      ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
