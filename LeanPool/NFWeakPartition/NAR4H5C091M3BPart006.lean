/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C091M3BPart006Block001


/-! NF weak partition development: NAR4H5C091M3BPart006. -/


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

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0009`. -/
@[expose]
noncomputable def nb091SplitAlpha0009 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy125 D R), (nb091AlphaDummy126 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)),
        ((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy125 D R))
          (Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy125 D R))
            (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCphi (Class.cv (nb091AlphaDummy120 D R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy126 R p))
          (Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy126 R p))
            (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCphi (Class.cv (nb091AlphaDummy122 R p))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy120 D R) from (by
                      unfold nb091AlphaDummy120;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
                  (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy122 R p) from (by
                      unfold nb091AlphaDummy122;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0118 R p) 1)))) (TAlphaVar.there
                    (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy119 D R) from (by
                        unfold nb091AlphaDummy119;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
                    (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy121 R p) from (by
                        unfold nb091AlphaDummy121;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy125 D R) from (by
                          unfold nb091AlphaDummy125;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0120 D R) 0))))
                      (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy126 R p) from (by
                          unfold nb091AlphaDummy126;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0121 R p) 0))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy123 D R) from (by
                            unfold nb091AlphaDummy123;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0117 D R) 0))))
                        (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy124 R p) from (by
                            unfold nb091AlphaDummy124;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0119 R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
                      ((Class.cv (nb091AlphaDummy105 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
                      ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091AlphaDummy120 D R) ≠ (nb091AlphaDummy127 D R) from
                            (by
                              unfold nb091AlphaDummy127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0122 D R) 0))))
                          (show (nb091AlphaDummy122 R p) ≠ (nb091AlphaDummy129 R p) from
                            (by
                              unfold nb091AlphaDummy129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0123 R p) 0))))
                          (TAlphaVar.there (show
                              (nb091AlphaDummy120 D R) ≠ (nb091AlphaDummy128 D R) from (by
                                unfold nb091AlphaDummy128;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0122 D R) 1)))) (show
                              (nb091AlphaDummy122 R p) ≠ (nb091AlphaDummy130 R p) from (by
                                unfold nb091AlphaDummy130;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0123 R p) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091AlphaDummy120 D R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb091AlphaDummy122 R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy134 D R) from
        (by
          unfold nb091AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R) 1)))) (show (nb091AlphaDummy129 R p) ≠
        (nb091AlphaDummy137 R p) from (by
          unfold nb091AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p) 1)))) (TAlphaVar.there (show
        (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy133 D R) from (by
          unfold nb091AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  0)))) (show (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy136 R p) from (by
          unfold nb091AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy127 D R) ≠
        (nb091AlphaDummy131 D R) from (by
          unfold nb091AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R)
                  0)))) (show (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy132 R p) from (by
          unfold nb091AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy135 D R), (nb091AlphaDummy138 R p)),
        ((nb091AlphaDummy134 D R), (nb091AlphaDummy137 R p)),
        ((nb091AlphaDummy133 D R), (nb091AlphaDummy136 R p)),
        ((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
        ((nb091AlphaDummy127 D R), (nb091AlphaDummy129 R p)),
        ((nb091AlphaDummy128 D R), (nb091AlphaDummy130 R p)),
        ((nb091AlphaDummy120 D R), (nb091AlphaDummy122 R p)),
        ((nb091AlphaDummy119 D R), (nb091AlphaDummy121 R p)),
        ((nb091AlphaDummy125 D R), (nb091AlphaDummy126 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)),
        ((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy135 D R), (nb091AlphaDummy138 R p)),
        ((nb091AlphaDummy134 D R), (nb091AlphaDummy137 R p)),
        ((nb091AlphaDummy133 D R), (nb091AlphaDummy136 R p)),
        ((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
        ((nb091AlphaDummy127 D R), (nb091AlphaDummy129 R p)),
        ((nb091AlphaDummy128 D R), (nb091AlphaDummy130 R p)),
        ((nb091AlphaDummy120 D R), (nb091AlphaDummy122 R p)),
        ((nb091AlphaDummy119 D R), (nb091AlphaDummy121 R p)),
        ((nb091AlphaDummy125 D R), (nb091AlphaDummy126 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)),
        ((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy129 R
        p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy145 D R) from
        (by
          unfold
            nb091AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy146 R p) from (by
          unfold
            nb091AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy145 D R) from
        (by
          unfold
            nb091AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy146 R p) from (by
          unfold
            nb091AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy135
        D R) ≠ (nb091AlphaDummy147 D R) from (by
          unfold
            nb091AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy148 R p) from (by
          unfold
            nb091AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy135
        D R) ≠ (nb091AlphaDummy147 D R) from (by
          unfold
            nb091AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy148 R p) from (by
          unfold
            nb091AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy131 D R)
                                      from (by
                                        unfold nb091AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy132 R p)
                                      from (by
                                        unfold nb091AlphaDummy132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
                                    ((nb091AlphaDummy127 D R), (nb091AlphaDummy129 R p)),
                                    ((nb091AlphaDummy128 D R), (nb091AlphaDummy130 R p)),
                                    ((nb091AlphaDummy120 D R), (nb091AlphaDummy122 R p)),
                                    ((nb091AlphaDummy119 D R), (nb091AlphaDummy121 R p)),
                                    ((nb091AlphaDummy125 D R), (nb091AlphaDummy126 R p)),
                                    ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)),
                                    ((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
                                    ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
                                    ((nb091AlphaDummy103 D R),
                                      (nb091AlphaDummy104 D R p)),
                                    ((nb091AlphaDummy101 D R),
                                      (nb091AlphaDummy102 D R p)),
                                    ((nb091AlphaDummy048 D R),
                                      (nb091AlphaDummy050 D R p)),
                                    ((nb091AlphaDummy047 D R),
                                      (nb091AlphaDummy049 D R p)),
                                    ((nb091AlphaDummy177 D R),
                                      (nb091AlphaDummy178 D R p)),
                                    ((nb091AlphaDummy051 D R),
                                      (nb091AlphaDummy052 D R p)),
                                    ((nb091AlphaDummy045 D R),
                                      (nb091AlphaDummy046 D R p)),
                                    ((nb091AlphaDummy042 D R),
                                      (nb091AlphaDummy044 D R p)),
                                    ((nb091AlphaDummy041 D R),
                                      (nb091AlphaDummy043 D R p)),
                                    ((nb091AlphaDummy001 D R),
                                      (nb091AlphaDummy002 D R p)),
                                    ((nb091AlphaDummy000 D R), p),
                                    ((nb091AlphaDummy003 D R),
                                      (nb091AlphaDummy004 D R p))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy131 D R)
                                    from (by
                                      unfold nb091AlphaDummy131;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0124 D R)
                                              0)))) (show (nb091AlphaDummy129 R p) ≠
                                      (nb091AlphaDummy132 R p) from (by
                                      unfold nb091AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0125 R p)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy131 D R)
                                      from (by
                                        unfold nb091AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy132 R p)
                                      from (by
                                        unfold nb091AlphaDummy132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
                                    ((nb091AlphaDummy127 D R), (nb091AlphaDummy129 R p)),
                                    ((nb091AlphaDummy128 D R), (nb091AlphaDummy130 R p)),
                                    ((nb091AlphaDummy120 D R), (nb091AlphaDummy122 R p)),
                                    ((nb091AlphaDummy119 D R), (nb091AlphaDummy121 R p)),
                                    ((nb091AlphaDummy125 D R), (nb091AlphaDummy126 R p)),
                                    ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)),
                                    ((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
                                    ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
                                    ((nb091AlphaDummy103 D R),
                                      (nb091AlphaDummy104 D R p)),
                                    ((nb091AlphaDummy101 D R),
                                      (nb091AlphaDummy102 D R p)),
                                    ((nb091AlphaDummy048 D R),
                                      (nb091AlphaDummy050 D R p)),
                                    ((nb091AlphaDummy047 D R),
                                      (nb091AlphaDummy049 D R p)),
                                    ((nb091AlphaDummy177 D R),
                                      (nb091AlphaDummy178 D R p)),
                                    ((nb091AlphaDummy051 D R),
                                      (nb091AlphaDummy052 D R p)),
                                    ((nb091AlphaDummy045 D R),
                                      (nb091AlphaDummy046 D R p)),
                                    ((nb091AlphaDummy042 D R),
                                      (nb091AlphaDummy044 D R p)),
                                    ((nb091AlphaDummy041 D R),
                                      (nb091AlphaDummy043 D R p)),
                                    ((nb091AlphaDummy001 D R),
                                      (nb091AlphaDummy002 D R p)),
                                    ((nb091AlphaDummy000 D R), p),
                                    ((nb091AlphaDummy003 D R),
                                      (nb091AlphaDummy004 D R p))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy120 D R) from (by
                        unfold nb091AlphaDummy120;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
                    (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy122 R p) from (by
                        unfold nb091AlphaDummy122;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0118 R p) 1))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy119 D R) from (by
                          unfold nb091AlphaDummy119;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
                      (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy121 R p) from (by
                          unfold nb091AlphaDummy121;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy125 D R) from (by
                            unfold nb091AlphaDummy125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0120 D R) 0))))
                        (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy126 R p) from (by
                            unfold nb091AlphaDummy126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0121 R p) 0))))
                        (TAlphaVar.there
                          (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy123 D R) from
                            (by
                              unfold nb091AlphaDummy123;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0117 D R) 0))))
                          (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy124 R p) from
                            (by
                              unfold nb091AlphaDummy124;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0119 R p) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
                        ((Class.cv (nb091AlphaDummy105 D R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
                        ((Class.cv (nb091AlphaDummy107 R p))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091AlphaDummy120 D R) ≠ (nb091AlphaDummy127 D R) from (by
                                unfold nb091AlphaDummy127;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0122 D R) 0)))) (show
                              (nb091AlphaDummy122 R p) ≠ (nb091AlphaDummy129 R p) from (by
                                unfold nb091AlphaDummy129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0123 R p) 0))))
                            (TAlphaVar.there (show
                                (nb091AlphaDummy120 D R) ≠ (nb091AlphaDummy128 D R) from
                                (by
                                  unfold nb091AlphaDummy128;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0122 D R)
                                          1)))) (show
                                (nb091AlphaDummy122 R p) ≠ (nb091AlphaDummy130 R p) from
                                (by
                                  unfold nb091AlphaDummy130;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0123 R p)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb091AlphaDummy120 D R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb091AlphaDummy122 R p))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy134 D R) from (by
          unfold nb091AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  1)))) (show (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy137 R p) from (by
          unfold nb091AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy127 D R) ≠
        (nb091AlphaDummy133 D R) from (by
          unfold nb091AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  0)))) (show (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy136 R p) from (by
          unfold nb091AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy127 D R) ≠
        (nb091AlphaDummy131 D R) from (by
          unfold nb091AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R)
                  0)))) (show (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy132 R p) from (by
          unfold nb091AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy135 D R), (nb091AlphaDummy138 R p)),
        ((nb091AlphaDummy134 D R), (nb091AlphaDummy137 R p)),
        ((nb091AlphaDummy133 D R), (nb091AlphaDummy136 R p)),
        ((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
        ((nb091AlphaDummy127 D R), (nb091AlphaDummy129 R p)),
        ((nb091AlphaDummy128 D R), (nb091AlphaDummy130 R p)),
        ((nb091AlphaDummy120 D R), (nb091AlphaDummy122 R p)),
        ((nb091AlphaDummy119 D R), (nb091AlphaDummy121 R p)),
        ((nb091AlphaDummy125 D R), (nb091AlphaDummy126 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)),
        ((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠ (nb091AlphaDummy141 D R) from
        (by
          unfold
            nb091AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy142 R p) from (by
          unfold
            nb091AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy139 D R) from (by
          unfold
            nb091AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy140 R p) from (by
          unfold
            nb091AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy135 D R), (nb091AlphaDummy138 R p)),
        ((nb091AlphaDummy134 D R), (nb091AlphaDummy137 R p)),
        ((nb091AlphaDummy133 D R), (nb091AlphaDummy136 R p)),
        ((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
        ((nb091AlphaDummy127 D R), (nb091AlphaDummy129 R p)),
        ((nb091AlphaDummy128 D R), (nb091AlphaDummy130 R p)),
        ((nb091AlphaDummy120 D R), (nb091AlphaDummy122 R p)),
        ((nb091AlphaDummy119 D R), (nb091AlphaDummy121 R p)),
        ((nb091AlphaDummy125 D R), (nb091AlphaDummy126 R p)),
        ((nb091AlphaDummy123 D R), (nb091AlphaDummy124 R p)),
        ((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy177 D R), (nb091AlphaDummy178 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy129 R
        p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy145 D R) from
        (by
          unfold
            nb091AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy146 R p) from (by
          unfold
            nb091AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠ (nb091AlphaDummy145 D R) from
        (by
          unfold
            nb091AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy146 R p) from (by
          unfold
            nb091AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy134 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091AlphaDummy137 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy127
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy135
        D R) ≠ (nb091AlphaDummy147 D R) from (by
          unfold
            nb091AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy148 R p) from (by
          unfold
            nb091AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy135
        D R) ≠ (nb091AlphaDummy147 D R) from (by
          unfold
            nb091AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy148 R p) from (by
          unfold
            nb091AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy135 D R) ≠
        (nb091AlphaDummy143 D R) from (by
          unfold
            nb091AlphaDummy143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091AlphaDummy138 R p) ≠ (nb091AlphaDummy144 R p) from (by
          unfold
            nb091AlphaDummy144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091AlphaDummy127 D R) ≠
        (nb091AlphaDummy131 D R) from (by
                                          unfold nb091AlphaDummy131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0124 D R) 0)))) (show
                                        (nb091AlphaDummy129 R p) ≠
        (nb091AlphaDummy132 R p) from (by
                                          unfold nb091AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0125 R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
                                      ((nb091AlphaDummy127 D R),
                                        (nb091AlphaDummy129 R p)),
                                      ((nb091AlphaDummy128 D R),
                                        (nb091AlphaDummy130 R p)),
                                      ((nb091AlphaDummy120 D R),
                                        (nb091AlphaDummy122 R p)),
                                      ((nb091AlphaDummy119 D R),
                                        (nb091AlphaDummy121 R p)),
                                      ((nb091AlphaDummy125 D R),
                                        (nb091AlphaDummy126 R p)),
                                      ((nb091AlphaDummy123 D R),
                                        (nb091AlphaDummy124 R p)),
                                      ((nb091AlphaDummy106 D R),
                                        (nb091AlphaDummy108 R p)),
                                      ((nb091AlphaDummy105 D R),
                                        (nb091AlphaDummy107 R p)),
                                      ((nb091AlphaDummy103 D R),
                                        (nb091AlphaDummy104 D R p)),
                                      ((nb091AlphaDummy101 D R),
                                        (nb091AlphaDummy102 D R p)),
                                      ((nb091AlphaDummy048 D R),
                                        (nb091AlphaDummy050 D R p)),
                                      ((nb091AlphaDummy047 D R),
                                        (nb091AlphaDummy049 D R p)),
                                      ((nb091AlphaDummy177 D R),
                                        (nb091AlphaDummy178 D R p)),
                                      ((nb091AlphaDummy051 D R),
                                        (nb091AlphaDummy052 D R p)),
                                      ((nb091AlphaDummy045 D R),
                                        (nb091AlphaDummy046 D R p)),
                                      ((nb091AlphaDummy042 D R),
                                        (nb091AlphaDummy044 D R p)),
                                      ((nb091AlphaDummy041 D R),
                                        (nb091AlphaDummy043 D R p)),
                                      ((nb091AlphaDummy001 D R),
                                        (nb091AlphaDummy002 D R p)),
                                      ((nb091AlphaDummy000 D R), p),
                                      ((nb091AlphaDummy003 D R),
                                        (nb091AlphaDummy004 D R p))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy127 D R) ≠ (nb091AlphaDummy131 D R)
                                      from (by
                                        unfold nb091AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091AlphaDummy129 R p) ≠ (nb091AlphaDummy132 R p)
                                      from (by
                                        unfold nb091AlphaDummy132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091AlphaDummy127 D R) ≠
        (nb091AlphaDummy131 D R) from (by
                                          unfold nb091AlphaDummy131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0124 D R) 0)))) (show
                                        (nb091AlphaDummy129 R p) ≠
        (nb091AlphaDummy132 R p) from (by
                                          unfold nb091AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0125 R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb091AlphaDummy131 D R), (nb091AlphaDummy132 R p)),
                                      ((nb091AlphaDummy127 D R),
                                        (nb091AlphaDummy129 R p)),
                                      ((nb091AlphaDummy128 D R),
                                        (nb091AlphaDummy130 R p)),
                                      ((nb091AlphaDummy120 D R),
                                        (nb091AlphaDummy122 R p)),
                                      ((nb091AlphaDummy119 D R),
                                        (nb091AlphaDummy121 R p)),
                                      ((nb091AlphaDummy125 D R),
                                        (nb091AlphaDummy126 R p)),
                                      ((nb091AlphaDummy123 D R),
                                        (nb091AlphaDummy124 R p)),
                                      ((nb091AlphaDummy106 D R),
                                        (nb091AlphaDummy108 R p)),
                                      ((nb091AlphaDummy105 D R),
                                        (nb091AlphaDummy107 R p)),
                                      ((nb091AlphaDummy103 D R),
                                        (nb091AlphaDummy104 D R p)),
                                      ((nb091AlphaDummy101 D R),
                                        (nb091AlphaDummy102 D R p)),
                                      ((nb091AlphaDummy048 D R),
                                        (nb091AlphaDummy050 D R p)),
                                      ((nb091AlphaDummy047 D R),
                                        (nb091AlphaDummy049 D R p)),
                                      ((nb091AlphaDummy177 D R),
                                        (nb091AlphaDummy178 D R p)),
                                      ((nb091AlphaDummy051 D R),
                                        (nb091AlphaDummy052 D R p)),
                                      ((nb091AlphaDummy045 D R),
                                        (nb091AlphaDummy046 D R p)),
                                      ((nb091AlphaDummy042 D R),
                                        (nb091AlphaDummy044 D R p)),
                                      ((nb091AlphaDummy041 D R),
                                        (nb091AlphaDummy043 D R p)),
                                      ((nb091AlphaDummy001 D R),
                                        (nb091AlphaDummy002 D R p)),
                                      ((nb091AlphaDummy000 D R), p),
                                      ((nb091AlphaDummy003 D R),
                                        (nb091AlphaDummy004 D R p))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
