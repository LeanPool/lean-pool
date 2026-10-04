/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part014

/-! NF weak partition development: NAR4H5C095M3Part015. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0017`. -/
@[expose]
noncomputable def nb095SplitAlpha0017 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy139 D R S_cls E), (nb095AlphaDummy140 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
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
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
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
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
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
                                    ((nb095AlphaDummy013 D R S_cls E),
                                      (nb095AlphaDummy016 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
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
                                    ((nb095AlphaDummy013 D R S_cls E),
                                      (nb095AlphaDummy016 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
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
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
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
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
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
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
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
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0018`. -/
@[expose]
noncomputable def nb095SplitAlpha0018 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy167 D R S_cls E), (nb095AlphaDummy168 f)),
        ((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy167 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy167 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy134 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy168 f))
          (synCphi (Class.cv (nb095AlphaDummy136 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy168 f))
            (synCphi (Class.cv (nb095AlphaDummy136 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                      (nb095AlphaDummy141 D R S_cls E) from (by
                      unfold nb095AlphaDummy141;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E) 0))))
                  (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy143 f) from (by
                      unfold nb095AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0129 f) 0))))
                  (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                        (nb095AlphaDummy142 D R S_cls E) from (by
                        unfold nb095AlphaDummy142;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E) 1))))
                    (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy144 f) from (by
                        unfold nb095AlphaDummy144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0129 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy134 D R S_cls E) ≠
                          (nb095AlphaDummy167 D R S_cls E) from (by
                          unfold nb095AlphaDummy167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0158 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy168 f) from (by
                          unfold nb095AlphaDummy168;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0159 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                            (nb095AlphaDummy165 D R S_cls E) from (by
                            unfold nb095AlphaDummy165;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0156 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy166 f) from (by
                            unfold nb095AlphaDummy166;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy136 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy141 D R S_cls E) ≠
                                        (nb095AlphaDummy148 D R S_cls E) from (by
                                        unfold nb095AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0132 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy151 f) from
                                      (by
                                        unfold nb095AlphaDummy151;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0133 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy141 D R S_cls E) ≠
        (nb095AlphaDummy147 D R S_cls E) from (by
                                          unfold nb095AlphaDummy147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0132 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy143 f) ≠
        (nb095AlphaDummy150 f) from (by
                                          unfold nb095AlphaDummy150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0133 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy141 D R S_cls E) ≠ (nb095AlphaDummy145 D R S_cls E) from (by
          unfold nb095AlphaDummy145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0130 D R S_cls E)
                  0)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
          unfold nb095AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy149 D R S_cls E),
        (nb095AlphaDummy152 f)), ((nb095AlphaDummy148 D R S_cls E),
        (nb095AlphaDummy151 f)), ((nb095AlphaDummy147 D R S_cls E),
        (nb095AlphaDummy150 f)), ((nb095AlphaDummy145 D R S_cls E),
        (nb095AlphaDummy146 f)), ((nb095AlphaDummy141 D R S_cls E),
        (nb095AlphaDummy143 f)), ((nb095AlphaDummy142 D R S_cls E),
        (nb095AlphaDummy144 f)), ((nb095AlphaDummy167 D R S_cls E),
        (nb095AlphaDummy168 f)), ((nb095AlphaDummy165 D R S_cls E),
        (nb095AlphaDummy166 f)), ((nb095AlphaDummy134 D R S_cls E),
        (nb095AlphaDummy136 f)), ((nb095AlphaDummy133 D R S_cls E),
        (nb095AlphaDummy135 f)), ((nb095AlphaDummy163 D R S_cls E),
        (nb095AlphaDummy164 f)), ((nb095AlphaDummy137 D R S_cls E),
        (nb095AlphaDummy138 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy013 D R S_cls E),
        (nb095AlphaDummy016 f)), ((nb095AlphaDummy012 D R S_cls E),
        (nb095AlphaDummy015 f)), ((nb095AlphaDummy011 D R S_cls E),
        (nb095AlphaDummy014 f)), ((nb095AlphaDummy017 D R S_cls E),
        (nb095AlphaDummy018 f)), ((nb095AlphaDummy001 D R S_cls E), u),
                                        ((nb095AlphaDummy002 D R S_cls E), x),
                                        ((nb095AlphaDummy000 D R S_cls E), f)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy155 D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy155 D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy155 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠
        (nb095AlphaDummy155 D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
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
                                        [((nb095AlphaDummy149 D R S_cls E),
        (nb095AlphaDummy152 f)), ((nb095AlphaDummy148 D R S_cls E),
        (nb095AlphaDummy151 f)), ((nb095AlphaDummy147 D R S_cls E),
        (nb095AlphaDummy150 f)), ((nb095AlphaDummy145 D R S_cls E),
        (nb095AlphaDummy146 f)), ((nb095AlphaDummy141 D R S_cls E),
        (nb095AlphaDummy143 f)), ((nb095AlphaDummy142 D R S_cls E),
        (nb095AlphaDummy144 f)), ((nb095AlphaDummy167 D R S_cls E),
        (nb095AlphaDummy168 f)), ((nb095AlphaDummy165 D R S_cls E),
        (nb095AlphaDummy166 f)), ((nb095AlphaDummy134 D R S_cls E),
        (nb095AlphaDummy136 f)), ((nb095AlphaDummy133 D R S_cls E),
        (nb095AlphaDummy135 f)), ((nb095AlphaDummy163 D R S_cls E),
        (nb095AlphaDummy164 f)), ((nb095AlphaDummy137 D R S_cls E),
        (nb095AlphaDummy138 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy013 D R S_cls E),
        (nb095AlphaDummy016 f)), ((nb095AlphaDummy012 D R S_cls E),
        (nb095AlphaDummy015 f)), ((nb095AlphaDummy011 D R S_cls E),
        (nb095AlphaDummy014 f)), ((nb095AlphaDummy017 D R S_cls E),
        (nb095AlphaDummy018 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy159 D R S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠
        (nb095AlphaDummy159 D R S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
                                        (nb095_support_mem_0130 D R S_cls E) 0))))
                            (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
                                unfold nb095AlphaDummy146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
                            ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
                            ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
                            ((nb095AlphaDummy167 D R S_cls E), (nb095AlphaDummy168 f)),
                            ((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
                            ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
                            ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
                            ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
                            ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
                            ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                            ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                            ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                            ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                            ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                            ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                            ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy141 D R S_cls E) ≠
                              (nb095AlphaDummy145 D R S_cls E) from (by
                              unfold nb095AlphaDummy145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0130 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
                              unfold nb095AlphaDummy146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy141 D R S_cls E) ≠
                                (nb095AlphaDummy145 D R S_cls E) from (by
                                unfold nb095AlphaDummy145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0130 D R S_cls E) 0))))
                            (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
                                unfold nb095AlphaDummy146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
                            ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
                            ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
                            ((nb095AlphaDummy167 D R S_cls E), (nb095AlphaDummy168 f)),
                            ((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
                            ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
                            ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
                            ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
                            ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
                            ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                            ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                            ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                            ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                            ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                            ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                            ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                        (nb095AlphaDummy141 D R S_cls E) from (by
                        unfold nb095AlphaDummy141;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E) 0))))
                    (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy143 f) from (by
                        unfold nb095AlphaDummy143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0129 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy134 D R S_cls E) ≠
                          (nb095AlphaDummy142 D R S_cls E) from (by
                          unfold nb095AlphaDummy142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E)
                                  1))))
                      (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy144 f) from (by
                          unfold nb095AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0129 f) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                            (nb095AlphaDummy167 D R S_cls E) from (by
                            unfold nb095AlphaDummy167;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0158 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy168 f) from (by
                            unfold nb095AlphaDummy168;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0159 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy134 D R S_cls E) ≠
                              (nb095AlphaDummy165 D R S_cls E) from (by
                              unfold nb095AlphaDummy165;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0156 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy136 f) ≠ (nb095AlphaDummy166 f) from (by
                              unfold nb095AlphaDummy166;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy136 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy141 D R S_cls E) ≠
        (nb095AlphaDummy148 D R S_cls E) from (by
                                          unfold nb095AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0132 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy143 f) ≠
        (nb095AlphaDummy151 f) from (by
                                          unfold nb095AlphaDummy151;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0133 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy141 D R S_cls E) ≠ (nb095AlphaDummy147 D R S_cls E) from (by
          unfold nb095AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R S_cls E)
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
                  (nb095_support_mem_0130 D R S_cls E)
                  0)))) (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
          unfold nb095AlphaDummy146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy149 D R S_cls E),
        (nb095AlphaDummy152 f)), ((nb095AlphaDummy148 D R S_cls E),
        (nb095AlphaDummy151 f)), ((nb095AlphaDummy147 D R S_cls E),
        (nb095AlphaDummy150 f)), ((nb095AlphaDummy145 D R S_cls E),
        (nb095AlphaDummy146 f)), ((nb095AlphaDummy141 D R S_cls E),
        (nb095AlphaDummy143 f)), ((nb095AlphaDummy142 D R S_cls E),
        (nb095AlphaDummy144 f)), ((nb095AlphaDummy167 D R S_cls E),
        (nb095AlphaDummy168 f)), ((nb095AlphaDummy165 D R S_cls E),
        (nb095AlphaDummy166 f)), ((nb095AlphaDummy134 D R S_cls E),
        (nb095AlphaDummy136 f)), ((nb095AlphaDummy133 D R S_cls E),
        (nb095AlphaDummy135 f)), ((nb095AlphaDummy163 D R S_cls E),
        (nb095AlphaDummy164 f)), ((nb095AlphaDummy137 D R S_cls E),
        (nb095AlphaDummy138 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy013 D R S_cls E),
        (nb095AlphaDummy016 f)), ((nb095AlphaDummy012 D R S_cls E),
        (nb095AlphaDummy015 f)), ((nb095AlphaDummy011 D R S_cls E),
        (nb095AlphaDummy014 f)), ((nb095AlphaDummy017 D R S_cls E),
        (nb095AlphaDummy018 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy155 D R S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy155 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy152 f) ≠ (nb095AlphaDummy154 f) from (by
          unfold
            nb095AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy155 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy155 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
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
        ((nb095AlphaDummy167 D R S_cls E), (nb095AlphaDummy168 f)),
        ((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy141 D R S_cls
        E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy159 D R S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy159 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy149 D R S_cls E) ≠ (nb095AlphaDummy161 D R S_cls E) from (by
          unfold
            nb095AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
                                          (nb095_support_mem_0130 D R S_cls E) 0))))
                              (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from
                                (by
                                  unfold nb095AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
                              ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
                              ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
                              ((nb095AlphaDummy167 D R S_cls E), (nb095AlphaDummy168 f)),
                              ((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
                              ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
                              ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
                              ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
                              ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
                              ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                              ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                              ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                              ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                              ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                              ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                              ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
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
                                        (nb095_support_mem_0130 D R S_cls E) 0))))
                            (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from (by
                                unfold nb095AlphaDummy146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy141 D R S_cls E) ≠
                                  (nb095AlphaDummy145 D R S_cls E) from (by
                                  unfold nb095AlphaDummy145;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0130 D R S_cls E) 0))))
                              (show (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy146 f) from
                                (by
                                  unfold nb095AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy145 D R S_cls E), (nb095AlphaDummy146 f)),
                              ((nb095AlphaDummy141 D R S_cls E), (nb095AlphaDummy143 f)),
                              ((nb095AlphaDummy142 D R S_cls E), (nb095AlphaDummy144 f)),
                              ((nb095AlphaDummy167 D R S_cls E), (nb095AlphaDummy168 f)),
                              ((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
                              ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
                              ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
                              ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
                              ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
                              ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
                              ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
                              ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
                              ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
                              ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
                              ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
                              ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0019`. -/
@[expose]
noncomputable def nb095SplitAlpha0019 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy175 D R S_cls E))
          (Class.cab (nb095AlphaDummy169 D R S_cls E)
            (synWrex (nb095AlphaDummy170 D R S_cls E)
              (Class.cv (nb095AlphaDummy013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy175 D R S_cls E))
            (Class.cab (nb095AlphaDummy169 D R S_cls E)
              (synWrex (nb095AlphaDummy170 D R S_cls E)
                (Class.cv (nb095AlphaDummy013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy169 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy170 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy176 f))
          (Class.cab (nb095AlphaDummy171 f)
            (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                (synCphi (Class.cv (nb095AlphaDummy172 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy176 f))
            (Class.cab (nb095AlphaDummy171 f)
              (synWrex (nb095AlphaDummy172 f) (Class.cv (nb095AlphaDummy016 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy171 f))
                  (synCphi (Class.cv (nb095AlphaDummy172 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                      (nb095AlphaDummy170 D R S_cls E) from (by
                      unfold nb095AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
                  (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy172 f) from (by
                      unfold nb095AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0174 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                        (nb095AlphaDummy169 D R S_cls E) from (by
                        unfold nb095AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 0))))
                    (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy171 f) from (by
                        unfold nb095AlphaDummy171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0174 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy013 D R S_cls E) ≠
                          (nb095AlphaDummy175 D R S_cls E) from (by
                          unfold nb095AlphaDummy175;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0176 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy176 f) from (by
                          unfold nb095AlphaDummy176;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0177 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                            (nb095AlphaDummy173 D R S_cls E) from (by
                            unfold nb095AlphaDummy173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0173 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy174 f) from (by
                            unfold nb095AlphaDummy174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0175 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy016 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                              (nb095AlphaDummy177 D R S_cls E) from (by
                              unfold nb095AlphaDummy177;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy179 f) from (by
                              unfold nb095AlphaDummy179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                (nb095AlphaDummy178 D R S_cls E) from (by
                                unfold nb095AlphaDummy178;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 1))))
                            (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy180 f) from (by
                                unfold nb095AlphaDummy180;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy172 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy184 D R S_cls E) from (by
          unfold nb095AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy187 f) from (by
          unfold nb095AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy183 D R S_cls E) from (by
          unfold nb095AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy186 f) from (by
          unfold nb095AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy181 D R S_cls E) from (by
          unfold nb095AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from (by
          unfold nb095AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy184
        D R S_cls E) ≠ (nb095AlphaDummy191 D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy177 D R S_cls E) ≠
                                        (nb095AlphaDummy181 D R S_cls E) from (by
                                        unfold nb095AlphaDummy181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                      (by
                                        unfold nb095AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy181 D R S_cls E),
                                      (nb095AlphaDummy182 f)),
                                    ((nb095AlphaDummy177 D R S_cls E),
                                      (nb095AlphaDummy179 f)),
                                    ((nb095AlphaDummy178 D R S_cls E),
                                      (nb095AlphaDummy180 f)),
                                    ((nb095AlphaDummy170 D R S_cls E),
                                      (nb095AlphaDummy172 f)),
                                    ((nb095AlphaDummy169 D R S_cls E),
                                      (nb095AlphaDummy171 f)),
                                    ((nb095AlphaDummy175 D R S_cls E),
                                      (nb095AlphaDummy176 f)),
                                    ((nb095AlphaDummy173 D R S_cls E),
                                      (nb095AlphaDummy174 f)),
                                    ((nb095AlphaDummy013 D R S_cls E),
                                      (nb095AlphaDummy016 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy177 D R S_cls E) ≠
                                      (nb095AlphaDummy181 D R S_cls E) from (by
                                      unfold nb095AlphaDummy181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                    (by
                                      unfold nb095AlphaDummy182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy177 D R S_cls E) ≠
                                        (nb095AlphaDummy181 D R S_cls E) from (by
                                        unfold nb095AlphaDummy181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                      (by
                                        unfold nb095AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy181 D R S_cls E),
                                      (nb095AlphaDummy182 f)),
                                    ((nb095AlphaDummy177 D R S_cls E),
                                      (nb095AlphaDummy179 f)),
                                    ((nb095AlphaDummy178 D R S_cls E),
                                      (nb095AlphaDummy180 f)),
                                    ((nb095AlphaDummy170 D R S_cls E),
                                      (nb095AlphaDummy172 f)),
                                    ((nb095AlphaDummy169 D R S_cls E),
                                      (nb095AlphaDummy171 f)),
                                    ((nb095AlphaDummy175 D R S_cls E),
                                      (nb095AlphaDummy176 f)),
                                    ((nb095AlphaDummy173 D R S_cls E),
                                      (nb095AlphaDummy174 f)),
                                    ((nb095AlphaDummy013 D R S_cls E),
                                      (nb095AlphaDummy016 f)),
                                    ((nb095AlphaDummy012 D R S_cls E),
                                      (nb095AlphaDummy015 f)),
                                    ((nb095AlphaDummy011 D R S_cls E),
                                      (nb095AlphaDummy014 f)),
                                    ((nb095AlphaDummy017 D R S_cls E),
                                      (nb095AlphaDummy018 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                        (nb095AlphaDummy170 D R S_cls E) from (by
                        unfold nb095AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
                    (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy172 f) from (by
                        unfold nb095AlphaDummy172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0174 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy013 D R S_cls E) ≠
                          (nb095AlphaDummy169 D R S_cls E) from (by
                          unfold nb095AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy171 f) from (by
                          unfold nb095AlphaDummy171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0174 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                            (nb095AlphaDummy175 D R S_cls E) from (by
                            unfold nb095AlphaDummy175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0176 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy176 f) from (by
                            unfold nb095AlphaDummy176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0177 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
                              (nb095AlphaDummy173 D R S_cls E) from (by
                              unfold nb095AlphaDummy173;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0173 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy174 f) from (by
                              unfold nb095AlphaDummy174;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0175 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy016 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy170 D R S_cls E) ≠
                                (nb095AlphaDummy177 D R S_cls E) from (by
                                unfold nb095AlphaDummy177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 0))))
                            (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy179 f) from (by
                                unfold nb095AlphaDummy179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy170 D R S_cls E) ≠
                                  (nb095AlphaDummy178 D R S_cls E) from (by
                                  unfold nb095AlphaDummy178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0178 D R S_cls E) 1))))
                              (show (nb095AlphaDummy172 f) ≠ (nb095AlphaDummy180 f) from
                                (by
                                  unfold nb095AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy172 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy184 D R S_cls E) from (by
          unfold nb095AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy187 f) from (by
          unfold nb095AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy183 D R S_cls E) from (by
          unfold nb095AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy186 f) from (by
          unfold nb095AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
          unfold nb095AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from (by
          unfold nb095AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy184
        D R S_cls E) ≠ (nb095AlphaDummy191 D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠ (nb095AlphaDummy191
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy192 f) from (by
          unfold
            nb095AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy189 D R S_cls E) from (by
          unfold
            nb095AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy190 f) from (by
          unfold
            nb095AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy185 D R S_cls E), (nb095AlphaDummy188 f)),
        ((nb095AlphaDummy184 D R S_cls E), (nb095AlphaDummy187 f)),
        ((nb095AlphaDummy183 D R S_cls E), (nb095AlphaDummy186 f)),
        ((nb095AlphaDummy181 D R S_cls E), (nb095AlphaDummy182 f)),
        ((nb095AlphaDummy177 D R S_cls E), (nb095AlphaDummy179 f)),
        ((nb095AlphaDummy178 D R S_cls E), (nb095AlphaDummy180 f)),
        ((nb095AlphaDummy170 D R S_cls E), (nb095AlphaDummy172 f)),
        ((nb095AlphaDummy169 D R S_cls E), (nb095AlphaDummy171 f)),
        ((nb095AlphaDummy175 D R S_cls E), (nb095AlphaDummy176 f)),
        ((nb095AlphaDummy173 D R S_cls E), (nb095AlphaDummy174 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy195
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy196 f) from (by
          unfold
            nb095AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy184 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy177
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy185
        D R S_cls E) ≠ (nb095AlphaDummy197 D R S_cls E) from (by
          unfold
            nb095AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy198 f) from (by
          unfold
            nb095AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy185 D R S_cls E) ≠
        (nb095AlphaDummy193 D R S_cls E) from (by
          unfold
            nb095AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy188 f) ≠ (nb095AlphaDummy194 f) from (by
          unfold
            nb095AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
                                          unfold nb095AlphaDummy181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy179 f) ≠
        (nb095AlphaDummy182 f) from (by
                                          unfold nb095AlphaDummy182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy181 D R S_cls E),
                                        (nb095AlphaDummy182 f)),
                                      ((nb095AlphaDummy177 D R S_cls E),
                                        (nb095AlphaDummy179 f)),
                                      ((nb095AlphaDummy178 D R S_cls E),
                                        (nb095AlphaDummy180 f)),
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy175 D R S_cls E),
                                        (nb095AlphaDummy176 f)),
                                      ((nb095AlphaDummy173 D R S_cls E),
                                        (nb095AlphaDummy174 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy177 D R S_cls E) ≠
                                        (nb095AlphaDummy181 D R S_cls E) from (by
                                        unfold nb095AlphaDummy181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy182 f) from
                                      (by
                                        unfold nb095AlphaDummy182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy177 D R S_cls E) ≠
        (nb095AlphaDummy181 D R S_cls E) from (by
                                          unfold nb095AlphaDummy181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy179 f) ≠
        (nb095AlphaDummy182 f) from (by
                                          unfold nb095AlphaDummy182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy181 D R S_cls E),
                                        (nb095AlphaDummy182 f)),
                                      ((nb095AlphaDummy177 D R S_cls E),
                                        (nb095AlphaDummy179 f)),
                                      ((nb095AlphaDummy178 D R S_cls E),
                                        (nb095AlphaDummy180 f)),
                                      ((nb095AlphaDummy170 D R S_cls E),
                                        (nb095AlphaDummy172 f)),
                                      ((nb095AlphaDummy169 D R S_cls E),
                                        (nb095AlphaDummy171 f)),
                                      ((nb095AlphaDummy175 D R S_cls E),
                                        (nb095AlphaDummy176 f)),
                                      ((nb095AlphaDummy173 D R S_cls E),
                                        (nb095AlphaDummy174 f)),
                                      ((nb095AlphaDummy013 D R S_cls E),
                                        (nb095AlphaDummy016 f)),
                                      ((nb095AlphaDummy012 D R S_cls E),
                                        (nb095AlphaDummy015 f)),
                                      ((nb095AlphaDummy011 D R S_cls E),
                                        (nb095AlphaDummy014 f)),
                                      ((nb095AlphaDummy017 D R S_cls E),
                                        (nb095AlphaDummy018 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
