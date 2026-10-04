/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part027

/-! NF weak partition development: NAR4H5C095M3Part028. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0055`. -/
@[expose]
noncomputable def nb095SplitAlpha0055 (x : Var) (u : Var) (D : Class) (R : Class)
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
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
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
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
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
                            ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                            ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                            ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                            ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                            ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                            ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                            ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                            ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                            ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                            ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                            ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                            ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
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
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                              ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                              ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                              ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                              ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                              ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                              ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                              ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                              ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                              ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                              ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                              ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                              ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0056`. -/
@[expose]
noncomputable def nb095SplitAlpha0056 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classEq (Class.cv (nb095AlphaDummy391 D R S_cls E))
          (synCop (Class.cv (nb095AlphaDummy385 D R S_cls E))
            (Class.cv (nb095AlphaDummy386 D R S_cls E)))) (Wff.neg
          (synWex (nb095AlphaDummy387 D R S_cls E) (synWa
              (synWbr (Class.cv (nb095AlphaDummy385 D R S_cls E))
                (synCcnv (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E))))
                (Class.cv (nb095AlphaDummy387 D R S_cls E)))
              (synWbr (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))
                (Class.cv (nb095AlphaDummy386 D R S_cls E)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb095AlphaDummy392 f))
          (synCop (Class.cv (nb095AlphaDummy388 f)) (Class.cv (nb095AlphaDummy389 f))))
        (Wff.neg (synWex (nb095AlphaDummy390 f) (synWa
              (synWbr (Class.cv (nb095AlphaDummy388 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb095AlphaDummy390 f)))
              (synWbr (Class.cv (nb095AlphaDummy390 f)) (synCcnv (Class.cv f))
                (Class.cv (nb095AlphaDummy389 f))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
              (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy391 D R S_cls E) from (by
                unfold nb095AlphaDummy391;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0392 D R S_cls E) 0))))) (Ne.symm
            (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy392 f) from (by
                unfold nb095AlphaDummy392;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0393 f) 0)))))
          (TAlphaVar.there (Ne.symm (show
                (nb095AlphaDummy385 D R S_cls E) ≠ (nb095AlphaDummy391 D R S_cls E) from
                (by
                  unfold nb095AlphaDummy391;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0390 D R S_cls E) 0))))) (Ne.symm
              (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy392 f) from (by
                  unfold nb095AlphaDummy392;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0391 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0037 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy386 D R S_cls E) ≠
                                      (nb095AlphaDummy394 D R S_cls E) from (by
                                      unfold nb095AlphaDummy394;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0422 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy396 f) from
                                    (by
                                      unfold nb095AlphaDummy396;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0424 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy386 D R S_cls E) ≠
                                        (nb095AlphaDummy393 D R S_cls E) from (by
                                        unfold nb095AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0422 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy395 f) from
                                      (by
                                        unfold nb095AlphaDummy395;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0424 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy423 D R S_cls E) from (by
                                          unfold nb095AlphaDummy423;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0426 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy389 f) ≠
        (nb095AlphaDummy424 f) from (by
                                          unfold nb095AlphaDummy424;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0427 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy397 D R S_cls E) from (by
          unfold nb095AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0423 D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy398 f) from (by
          unfold nb095AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0425 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy388 f))).fv ∪
                                      ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg
                                    (nb095SplitAlpha0038 x u D R S_cls f E)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy386 D R S_cls E) ≠
                                      (nb095AlphaDummy394 D R S_cls E) from (by
                                      unfold nb095AlphaDummy394;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0422 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy396 f) from
                                    (by
                                      unfold nb095AlphaDummy396;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0424 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy386 D R S_cls E) ≠
                                        (nb095AlphaDummy393 D R S_cls E) from (by
                                        unfold nb095AlphaDummy393;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0422 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy395 f) from
                                      (by
                                        unfold nb095AlphaDummy395;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0424 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy423 D R S_cls E) from (by
                                          unfold nb095AlphaDummy423;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0426 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy389 f) ≠
        (nb095AlphaDummy424 f) from (by
                                          unfold nb095AlphaDummy424;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0427 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy397 D R S_cls E) from (by
          unfold nb095AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0423 D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy398 f) from (by
          unfold nb095AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0425 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy385 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095AlphaDummy388 f))).fv ∪
                                      ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb095SplitAlpha0038 x u D R S_cls f
                                      E))))))))))))))))) (TAlphaWff.neg (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg
                        (TAlphaWff.neg (nb095SplitAlpha0039 x u D R S_cls f E)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy430 D R S_cls E) from (by
          unfold nb095AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0460 D R S_cls E)
                  1)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy432 f) from (by
          unfold nb095AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0462 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy429 D R S_cls E) from (by
          unfold nb095AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0460 D R S_cls E)
                  0)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy431 f) from (by
          unfold nb095AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0462 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy459 D R S_cls E) from (by
          unfold nb095AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0464 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy460 f) from (by
          unfold nb095AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0465 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy433 D R S_cls E) from (by
          unfold nb095AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0461 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy434 f) from (by
          unfold nb095AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0463 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy385 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy387 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0040 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy461 D R S_cls E), (nb095AlphaDummy462 f)),
        ((nb095AlphaDummy430 D R S_cls E), (nb095AlphaDummy432 f)),
        ((nb095AlphaDummy429 D R S_cls E), (nb095AlphaDummy431 f)),
        ((nb095AlphaDummy459 D R S_cls E), (nb095AlphaDummy460 f)),
        ((nb095AlphaDummy433 D R S_cls E), (nb095AlphaDummy434 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy430 D R S_cls E) from (by
          unfold nb095AlphaDummy430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0460 D R S_cls E)
                  1)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy432 f) from (by
          unfold nb095AlphaDummy432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0462 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy429 D R S_cls E) from (by
          unfold nb095AlphaDummy429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0460 D R S_cls E)
                  0)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy431 f) from (by
          unfold nb095AlphaDummy431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0462 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy459 D R S_cls E) from (by
          unfold nb095AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0464 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy460 f) from (by
          unfold nb095AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0465 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy387 D R S_cls E) ≠ (nb095AlphaDummy433 D R S_cls E) from (by
          unfold nb095AlphaDummy433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0461 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy434 f) from (by
          unfold nb095AlphaDummy434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0463 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy385 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy387 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy388 f))).fv ∪ ((Class.cv (nb095AlphaDummy390 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0040 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy461 D R S_cls E), (nb095AlphaDummy462 f)),
        ((nb095AlphaDummy430 D R S_cls E), (nb095AlphaDummy432 f)),
        ((nb095AlphaDummy429 D R S_cls E), (nb095AlphaDummy431 f)),
        ((nb095AlphaDummy459 D R S_cls E), (nb095AlphaDummy460 f)),
        ((nb095AlphaDummy433 D R S_cls E), (nb095AlphaDummy434 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.neg (nb095SplitAlpha0049 x u D R S_cls f E dv_f_u dv_f_x))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg
                        (TAlphaWff.neg (nb095SplitAlpha0050 x u D R S_cls f E)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) from (by
          unfold nb095AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R S_cls E)
                  1)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy546 f) from (by
          unfold nb095AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy573 D R S_cls E) from (by
          unfold nb095AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0594 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy574 f) from (by
          unfold nb095AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0595 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy547 D R S_cls E) from (by
          unfold nb095AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0591 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy548 f) from (by
          unfold nb095AlphaDummy548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0593 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCcnv (synCcnv
        (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy387 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy386 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0051 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) from (by
          unfold nb095AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R S_cls E)
                  1)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy546 f) from (by
          unfold nb095AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy573 D R S_cls E) from (by
          unfold nb095AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0594 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy574 f) from (by
          unfold nb095AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0595 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy547 D R S_cls E) from (by
          unfold nb095AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0591 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy548 f) from (by
          unfold nb095AlphaDummy548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0593 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCcnv (synCcnv
        (Class.cv (nb095AlphaDummy000 D R S_cls E))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095AlphaDummy387 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy386 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095SplitAlpha0051 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb095AlphaDummy092 D R S_cls E) ≠
                                (nb095AlphaDummy095 D R S_cls E) from (by
                                unfold nb095AlphaDummy095;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0082 D R S_cls E) 0))))) (Ne.symm
                            (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy096 f) from (by
                                unfold nb095AlphaDummy096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0083 f) 0)))))
                          (TAlphaVar.there (Ne.symm (show (nb095AlphaDummy091 D R S_cls E) ≠
                                  (nb095AlphaDummy095 D R S_cls E) from (by
                                  unfold nb095AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0080 D R S_cls E) 0))))) (Ne.symm
                              (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy096 f) from
                                (by
                                  unfold nb095AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0081 f) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095SplitAlpha0052 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0053 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129 D R S_cls
        E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E),
        (nb095AlphaDummy099 f)), ((nb095AlphaDummy127 D R S_cls E),
        (nb095AlphaDummy128 f)), ((nb095AlphaDummy101 D R S_cls E),
        (nb095AlphaDummy102 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0053 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129 D R S_cls
        E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E),
        (nb095AlphaDummy099 f)), ((nb095AlphaDummy127 D R S_cls E),
        (nb095AlphaDummy128 f)), ((nb095AlphaDummy101 D R S_cls E),
        (nb095AlphaDummy102 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095SplitAlpha0054 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
        ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0055 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy165 D R S_cls
        E), (nb095AlphaDummy166 f)), ((nb095AlphaDummy134 D R S_cls E),
        (nb095AlphaDummy136 f)), ((nb095AlphaDummy133 D R S_cls E),
        (nb095AlphaDummy135 f)), ((nb095AlphaDummy163 D R S_cls E),
        (nb095AlphaDummy164 f)), ((nb095AlphaDummy137 D R S_cls E),
        (nb095AlphaDummy138 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
        ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0055 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy165 D R S_cls
        E), (nb095AlphaDummy166 f)), ((nb095AlphaDummy134 D R S_cls E),
        (nb095AlphaDummy136 f)), ((nb095AlphaDummy133 D R S_cls E),
        (nb095AlphaDummy135 f)), ((nb095AlphaDummy163 D R S_cls E),
        (nb095AlphaDummy164 f)), ((nb095AlphaDummy137 D R S_cls E),
        (nb095AlphaDummy138 f)), ((nb095AlphaDummy092 D R S_cls E),
        (nb095AlphaDummy094 f)), ((nb095AlphaDummy091 D R S_cls E),
        (nb095AlphaDummy093 f)), ((nb095AlphaDummy095 D R S_cls E),
        (nb095AlphaDummy096 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095AlphaDummy000 D R S_cls E) ≠
                              (nb095AlphaDummy092 D R S_cls E) from (by
                              unfold nb095AlphaDummy092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0170 D R S_cls E)
                                      1)))) (show f ≠ (nb095AlphaDummy094 f) from (by
                              unfold nb095AlphaDummy094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0171 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                (nb095AlphaDummy091 D R S_cls E) from (by
                                unfold nb095AlphaDummy091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0170 D R S_cls E) 0))))
                            (show f ≠ (nb095AlphaDummy093 f) from (by
                                unfold nb095AlphaDummy093;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0171 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy095 D R S_cls E) from (by
                                  unfold nb095AlphaDummy095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0168 D R S_cls E) 0))))
                              (show f ≠ (nb095AlphaDummy096 f) from (by
                                  unfold nb095AlphaDummy096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0169 f) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                    (nb095AlphaDummy387 D R S_cls E) from (by
                                    unfold nb095AlphaDummy387;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0554 D R S_cls E) 2))))
                                (show f ≠ (nb095AlphaDummy390 f) from (by
                                    unfold nb095AlphaDummy390;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0556 f)
                                            2)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy386 D R S_cls E) from (by
                                      unfold nb095AlphaDummy386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0554 D R S_cls E) 1))))
                                  (show f ≠ (nb095AlphaDummy389 f) from (by
                                      unfold nb095AlphaDummy389;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0556 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy385 D R S_cls E) from (by
                                        unfold nb095AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0554 D R S_cls E) 0))))
                                    (show f ≠ (nb095AlphaDummy388 f) from (by
                                        unfold nb095AlphaDummy388;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0556 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy391 D R S_cls E) from (by
                                          unfold nb095AlphaDummy391;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0555 D R S_cls E)
                                                  0)))) (show f ≠ (nb095AlphaDummy392 f) from
                                        (by
                                          unfold nb095AlphaDummy392;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0557 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy383 D R S_cls E) from (by
          unfold nb095AlphaDummy383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0552 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy384 f) from (by
          unfold nb095AlphaDummy384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0553 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy381 D R S_cls E) from (by
          unfold nb095AlphaDummy381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0550 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy382 f) from (by
          unfold nb095AlphaDummy382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0551 f) 0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _)))))))))))))))))))))))

theorem nb095_wpp_notmem_1488 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy383 D R S_cls E) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy383, fv_syn_cid] using
    (nb095_compact_fv_empty_0312 D R S_cls E)

theorem nb095_wpp_notmem_1489 (f : Var) : (nb095AlphaDummy384 f) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy384, fv_syn_cid] using (nb095_compact_fv_empty_0313 f)

theorem nb095_wpp_notmem_1490 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy381 D R S_cls E) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy381, fv_syn_cid] using
    (nb095_compact_fv_empty_0314 D R S_cls E)

theorem nb095_wpp_notmem_1491 (f : Var) : (nb095AlphaDummy382 f) ∉ ((synCid)).fv := by
  simpa only [nb095AlphaDummy382, fv_syn_cid] using (nb095_compact_fv_empty_0315 f)

theorem nb095_compact_envfresh_0192 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TEnvFresh
      [((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy383 D R S_cls E) (nb095AlphaDummy384 f)
      (nb095_wpp_notmem_1488 D R S_cls E) (nb095_wpp_notmem_1489 f)
      (TEnvFresh.consFresh (nb095AlphaDummy381 D R S_cls E) (nb095AlphaDummy382 f)
        (nb095_wpp_notmem_1490 D R S_cls E) (nb095_wpp_notmem_1491 f)
        (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
          (nb095_wpp_notmem_0510 D R S_cls E) (nb095_wpp_notmem_0511 u)
          (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
            (nb095_wpp_notmem_0512 D R S_cls E) (nb095_wpp_notmem_0513 x)
            (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
              (nb095_wpp_notmem_0514 D R S_cls E) (nb095_wpp_notmem_0515 f)
              (TEnvFresh.nil ((synCid)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
