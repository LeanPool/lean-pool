/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part032`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0068`. -/
@[expose]
noncomputable def nb068SplitAlpha0068 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy145))
            (synCun (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy148 f))
            (synCun (Class.cv (nb068AlphaDummy149 f))
              (Class.cv (nb068AlphaDummy150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
          ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
          ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
          ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
          ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
          ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
          ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
          ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0069`. -/
@[expose]
noncomputable def nb068SplitAlpha0069 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy139))
          (Class.cv (nb068AlphaDummy132))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy140))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
              (Class.cv (nb068AlphaDummy139))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy141 f))
          (Class.cv (nb068AlphaDummy134 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
              (Class.cv (nb068AlphaDummy141 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
              unfold nb068AlphaDummy139;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 0))))
          (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy141 f) from (by
              unfold nb068AlphaDummy141;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
                unfold nb068AlphaDummy140;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 1))))
            (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy142 f) from (by
                unfold nb068AlphaDummy142;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
                  unfold nb068AlphaDummy165;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0162) 0))))
              (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy166 f) from (by
                  unfold nb068AlphaDummy166;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0163 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
                    unfold nb068AlphaDummy163;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0160) 0))))
                (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
                    unfold nb068AlphaDummy164;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0161 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                                  unfold nb068AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from
                                (by
                                  unfold nb068AlphaDummy149;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy145) from (by
                                    unfold nb068AlphaDummy145;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0136) 0)))) (show
                                  (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                                    unfold nb068AlphaDummy148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0137 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                                    (by
                                      unfold nb068AlphaDummy143;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0134)
                                              0)))) (show
                                    (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from
                                    (by
                                      unfold nb068AlphaDummy144;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0135 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                                  ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                                  ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                                  ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                                  ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                                  ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                                  ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                                  ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                                  ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0068 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                          unfold nb068AlphaDummy143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                          unfold nb068AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                      ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                      ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                      ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                      ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                      ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                      ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                      ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                      ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                      (by
                        unfold nb068AlphaDummy143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                    (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                        unfold nb068AlphaDummy144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                          unfold nb068AlphaDummy143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                          unfold nb068AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                      ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                      ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                      ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                      ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                      ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                      ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                      ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                      ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0070`. -/
@[expose]
noncomputable def nb068SplitAlpha0070 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy161))
          (Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy161))
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
          (Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                    (by
                      unfold nb068AlphaDummy132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                  (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                      unfold nb068AlphaDummy134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from
                      (by
                        unfold nb068AlphaDummy131;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                        unfold nb068AlphaDummy133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                          unfold nb068AlphaDummy161;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                          unfold nb068AlphaDummy162;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                            unfold nb068AlphaDummy135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                            unfold nb068AlphaDummy136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0069 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0069 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                      (by
                        unfold nb068AlphaDummy132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                        unfold nb068AlphaDummy134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from (by
                          unfold nb068AlphaDummy131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                          unfold nb068AlphaDummy133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                            unfold nb068AlphaDummy161;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                            unfold nb068AlphaDummy162;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                              unfold nb068AlphaDummy135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                          (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                              unfold nb068AlphaDummy136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy125))).fv ∪
                        ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0069 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0069 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                            ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                            ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                            ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                            ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                            ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                            ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                            ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                            ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                            ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0071`. -/
@[expose]
noncomputable def nb068SplitAlpha0071 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
        ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
        ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
        ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
          ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0072`. -/
@[expose]
noncomputable def nb068SplitAlpha0072 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy175))
            (Class.cv (nb068AlphaDummy168))) (Wff.classEq (Class.cv (nb068AlphaDummy176))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
              (Class.cv (nb068AlphaDummy175))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy177 f))
            (Class.cv (nb068AlphaDummy170 f)))
          (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
              (Class.cv (nb068AlphaDummy177 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
                unfold nb068AlphaDummy175;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0))))
            (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy177 f) from (by
                unfold nb068AlphaDummy177;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0))))
            (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
                  unfold nb068AlphaDummy176;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1))))
              (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy178 f) from (by
                  unfold nb068AlphaDummy178;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                                  unfold nb068AlphaDummy182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from
                                (by
                                  unfold nb068AlphaDummy185;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy181) from (by
                                    unfold nb068AlphaDummy181;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0174) 0)))) (show
                                  (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                                    unfold nb068AlphaDummy184;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0175 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                                    (by
                                      unfold nb068AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0172)
                                              0)))) (show
                                    (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                    (by
                                      unfold nb068AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0173 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                                  ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                                  ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                                  ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                                  ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                                  ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                                  ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0071 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                          unfold nb068AlphaDummy179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                          unfold nb068AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                      ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                      (by
                        unfold nb068AlphaDummy179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                    (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                        unfold nb068AlphaDummy180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                          unfold nb068AlphaDummy179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                          unfold nb068AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                      ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part033`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0073`. -/
@[expose]
noncomputable def nb068SplitAlpha0073 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
        ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
        ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
        ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
        ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
          ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
          ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
          ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0074`. -/
@[expose]
noncomputable def nb068SplitAlpha0074 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
        ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy175))
          (Class.cv (nb068AlphaDummy168))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy176))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
              (Class.cv (nb068AlphaDummy175))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy177 f))
          (Class.cv (nb068AlphaDummy170 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
              (Class.cv (nb068AlphaDummy177 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
              unfold nb068AlphaDummy175;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0))))
          (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy177 f) from (by
              unfold nb068AlphaDummy177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
                unfold nb068AlphaDummy176;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1))))
            (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy178 f) from (by
                unfold nb068AlphaDummy178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy201) from (by
                  unfold nb068AlphaDummy201;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0200) 0))))
              (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy202 f) from (by
                  unfold nb068AlphaDummy202;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0201 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
                    unfold nb068AlphaDummy199;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0198) 0))))
                (show (nb068AlphaDummy170 f) ≠ (nb068AlphaDummy200 f) from (by
                    unfold nb068AlphaDummy200;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0199 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                                  unfold nb068AlphaDummy182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from
                                (by
                                  unfold nb068AlphaDummy185;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy181) from (by
                                    unfold nb068AlphaDummy181;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0174) 0)))) (show
                                  (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                                    unfold nb068AlphaDummy184;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0175 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                                    (by
                                      unfold nb068AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0172)
                                              0)))) (show
                                    (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                    (by
                                      unfold nb068AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0173 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                                  ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                                  ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                                  ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                                  ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                                  ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                                  ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                                  ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                                  ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0073 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                          unfold nb068AlphaDummy179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                          unfold nb068AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                      ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                      ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                      (by
                        unfold nb068AlphaDummy179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                    (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                        unfold nb068AlphaDummy180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                          unfold nb068AlphaDummy179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                          unfold nb068AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                      ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                      ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                      ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                      ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                      ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                      ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                      ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                      ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                      ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                      ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                      ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                      ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                      ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0075`. -/
@[expose]
noncomputable def nb068SplitAlpha0075 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy197))
          (Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy197))
            (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy198 f))
          (Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy198 f))
            (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from
                    (by
                      unfold nb068AlphaDummy168;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                  (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                      unfold nb068AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from
                      (by
                        unfold nb068AlphaDummy167;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                    (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                        unfold nb068AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                          unfold nb068AlphaDummy197;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                          unfold nb068AlphaDummy198;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from (by
                            unfold nb068AlphaDummy171;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                            unfold nb068AlphaDummy172;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy126))).fv ∪
                      ((Class.cv (nb068AlphaDummy125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0074 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0074 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                          ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                          ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from
                      (by
                        unfold nb068AlphaDummy168;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                    (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                        unfold nb068AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
                          unfold nb068AlphaDummy167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                          unfold nb068AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                            unfold nb068AlphaDummy197;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                            unfold nb068AlphaDummy198;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from (by
                              unfold nb068AlphaDummy171;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                          (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                              unfold nb068AlphaDummy172;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0074 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0074 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                            ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                            ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                            ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                            ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                            ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                            ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                            ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                            ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                            ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0076`. -/
@[expose]
noncomputable def nb068SplitAlpha0076 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
        ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy129))
          (synCop (Class.cv (nb068AlphaDummy125)) (Class.cv (nb068AlphaDummy126))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))))
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy130 f))
          (synCop (Class.cv (nb068AlphaDummy127 f)) (Class.cv (nb068AlphaDummy128 f))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy129) from (by
                unfold nb068AlphaDummy129;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0))))) (Ne.symm
            (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy130 f) from (by
                unfold nb068AlphaDummy130;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy129) from
                (by
                  unfold nb068AlphaDummy129;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
            (Ne.symm (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy130 f) from (by
                  unfold nb068AlphaDummy130;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                    (by
                                      unfold nb068AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from
                                    (by
                                      unfold nb068AlphaDummy134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
                                        unfold nb068AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068AlphaDummy127 f) ≠
                                        (nb068AlphaDummy133 f) from (by
                                        unfold nb068AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from
                                        (by
                                          unfold nb068AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
                                          unfold nb068AlphaDummy138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb068SplitAlpha0067 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                    (by
                                      unfold nb068AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from
                                    (by
                                      unfold nb068AlphaDummy134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
                                        unfold nb068AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068AlphaDummy127 f) ≠
                                        (nb068AlphaDummy133 f) from (by
                                        unfold nb068AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from
                                        (by
                                          unfold nb068AlphaDummy137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
                                          unfold nb068AlphaDummy138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb068SplitAlpha0067 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0070 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                        unfold nb068AlphaDummy168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy170 f) from (by
                                        unfold nb068AlphaDummy170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                        (by
                                          unfold nb068AlphaDummy167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy169 f) from (by
                                          unfold nb068AlphaDummy169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy126) ≠
        (nb068AlphaDummy173) from (by
          unfold nb068AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy174 f) from (by
          unfold nb068AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from (by
          unfold nb068AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
          unfold nb068AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb068SplitAlpha0072 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                        unfold nb068AlphaDummy168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy170 f) from (by
                                        unfold nb068AlphaDummy170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                        (by
                                          unfold nb068AlphaDummy167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy169 f) from (by
                                          unfold nb068AlphaDummy169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy126) ≠
        (nb068AlphaDummy173) from (by
          unfold nb068AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy174 f) from (by
          unfold nb068AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from (by
          unfold nb068AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
          unfold nb068AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy126))).fv ∪
                                        ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb068SplitAlpha0072 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0075 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy126) from (by
                unfold nb068AlphaDummy126;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1))))
            (show f ≠ (nb068AlphaDummy128 f) from (by
                unfold nb068AlphaDummy128;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy125) from (by
                  unfold nb068AlphaDummy125;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0))))
              (show f ≠ (nb068AlphaDummy127 f) from (by
                  unfold nb068AlphaDummy127;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy129) from (by
                    unfold nb068AlphaDummy129;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0210) 0))))
                (show f ≠ (nb068AlphaDummy130 f) from (by
                    unfold nb068AlphaDummy130;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy240) from
                    (by
                      unfold nb068AlphaDummy240;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0290) 1))))
                  (show f ≠ (nb068AlphaDummy242 f) from (by
                      unfold nb068AlphaDummy242;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0291 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy239) from
                      (by
                        unfold nb068AlphaDummy239;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0290) 0))))
                    (show f ≠ (nb068AlphaDummy241 f) from (by
                        unfold nb068AlphaDummy241;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0291 f) 0))))
                    (TAlphaVar.here _ _ _))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0077`. -/
@[expose]
noncomputable def nb068SplitAlpha0077 (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (synWfun (Class.cv (nb068AlphaDummy000))) (Wff.neg
          (Wff.classEq (synCdm (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy001)))))
      (Wff.imp (synWfun (Class.cv f))
        (Wff.neg (Wff.classEq (synCdm (Class.cv f)) (Class.cv x)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0033 x y f))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy051) from (by
                          unfold nb068AlphaDummy051;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0044) 0))))) (Ne.symm
                      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy052 f) from (by
                          unfold nb068AlphaDummy052;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0045 f) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy051) from (by
                            unfold nb068AlphaDummy051;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0042) 0))))) (Ne.symm
                        (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy052 f) from (by
                            unfold nb068AlphaDummy052;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0043 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
          unfold nb068AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 1)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy056 f) from (by
          unfold nb068AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy045) ≠ (nb068AlphaDummy053) from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy045) ≠ (nb068AlphaDummy059) from (by
          unfold nb068AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy060 f) from (by
          unfold nb068AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy057)
        from (by
          unfold nb068AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy058 f) from (by
          unfold nb068AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb068SplitAlpha0035 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy054) from (by
          unfold nb068AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 1)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy056 f) from (by
          unfold nb068AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy045) ≠ (nb068AlphaDummy053) from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy045) ≠ (nb068AlphaDummy059) from (by
          unfold nb068AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy060 f) from (by
          unfold nb068AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy057)
        from (by
          unfold nb068AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy058 f) from (by
          unfold nb068AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb068SplitAlpha0035 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb068SplitAlpha0038 x y f)))))))))
              (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0060 x y f)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb068AlphaDummy240), (nb068AlphaDummy242 f)),
                    ((nb068AlphaDummy239), (nb068AlphaDummy241 f)),
                    ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                    ((nb068AlphaDummy001), x),
                    ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                  (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy244) from (by
          unfold nb068AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 1)))) (show (nb068AlphaDummy242 f) ≠
        (nb068AlphaDummy246 f) from (by
          unfold nb068AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy240) ≠ (nb068AlphaDummy243) from (by
          unfold nb068AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 0)))) (show (nb068AlphaDummy242 f) ≠
        (nb068AlphaDummy245 f) from (by
          unfold nb068AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy240) ≠ (nb068AlphaDummy249) from (by
          unfold nb068AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0256) 0)))) (show (nb068AlphaDummy242 f) ≠
        (nb068AlphaDummy250 f) from (by
          unfold nb068AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0257 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy247)
        from (by
          unfold nb068AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0253)
                  0)))) (show (nb068AlphaDummy242 f) ≠ (nb068AlphaDummy248 f) from (by
          unfold nb068AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0255 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0062 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy244) from (by
          unfold nb068AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 1)))) (show (nb068AlphaDummy242 f) ≠
        (nb068AlphaDummy246 f) from (by
          unfold nb068AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy240) ≠ (nb068AlphaDummy243) from (by
          unfold nb068AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 0)))) (show (nb068AlphaDummy242 f) ≠
        (nb068AlphaDummy245 f) from (by
          unfold nb068AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy240) ≠ (nb068AlphaDummy249) from (by
          unfold nb068AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0256) 0)))) (show (nb068AlphaDummy242 f) ≠
        (nb068AlphaDummy250 f) from (by
          unfold nb068AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0257 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy247)
        from (by
          unfold nb068AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0253)
                  0)))) (show (nb068AlphaDummy242 f) ≠ (nb068AlphaDummy248 f) from (by
          unfold nb068AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0255 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0062 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb068SplitAlpha0065 x y f))))))))
                (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0076 x y f)))))))))
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_f_x)
            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
              (TAlphaVar.here _ _ _)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part034`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0078`. -/
@[expose]
noncomputable def nb068SplitAlpha0078 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
        ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
        ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
        ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
        ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
        ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
        ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
        ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy301))
            (synCun (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy304 f))
            (synCun (Class.cv (nb068AlphaDummy305 f))
              (Class.cv (nb068AlphaDummy306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
          ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
          ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
          ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
          ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
          ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
          ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0079`. -/
@[expose]
noncomputable def nb068SplitAlpha0079 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
        ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy287))
        (synCphi (Class.cv (nb068AlphaDummy288))))
      (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
        (synCphi (Class.cv (nb068AlphaDummy290 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy286 f))).fv ∪
            ((Class.cv (nb068AlphaDummy285 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy295) from (by
                    unfold nb068AlphaDummy295;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
                (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy297 f) from (by
                    unfold nb068AlphaDummy297;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy296) from
                    (by
                      unfold nb068AlphaDummy296;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
                  (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy298 f) from (by
                      unfold nb068AlphaDummy298;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068AlphaDummy288))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068AlphaDummy290 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy302) from
                                    (by
                                      unfold nb068AlphaDummy302;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0302)
                                              1)))) (show
                                    (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy305 f) from
                                    (by
                                      unfold nb068AlphaDummy305;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0303 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy295) ≠ (nb068AlphaDummy301) from (by
                                        unfold nb068AlphaDummy301;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0302)
                                                0)))) (show (nb068AlphaDummy297 f) ≠
                                        (nb068AlphaDummy304 f) from (by
                                        unfold nb068AlphaDummy304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0303 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from
                                        (by
                                          unfold nb068AlphaDummy299;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0300)
                                                  0)))) (show (nb068AlphaDummy297 f) ≠
        (nb068AlphaDummy300 f) from (by
                                          unfold nb068AlphaDummy300;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0301 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
                                      ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
                                      ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
                                      ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                                      ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                                      ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                                      ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                                      ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                                      ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
                                      ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                                      ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                                      ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                                      ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                                      ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                                      ((nb068AlphaDummy000), f),
                                      ((nb068AlphaDummy002), y),
                                      ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                        (nb068AlphaDummy004 x y f))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068SplitAlpha0078 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                              unfold nb068AlphaDummy299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                              unfold nb068AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                          ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
                          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                          ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                          ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                            unfold nb068AlphaDummy299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                        (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                            unfold nb068AlphaDummy300;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                              unfold nb068AlphaDummy299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                              unfold nb068AlphaDummy300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                          ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
                          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                          ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                          ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part035`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0080`. -/
@[expose]
noncomputable def nb068SplitAlpha0080 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
        ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
        ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
        ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
        ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
        ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
        ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
        ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
        ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
        ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy301))
            (synCun (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy304 f))
            (synCun (Class.cv (nb068AlphaDummy305 f))
              (Class.cv (nb068AlphaDummy306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
          ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
          ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
          ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
          ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
          ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
          ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
          ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
          ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0081`. -/
@[expose]
noncomputable def nb068SplitAlpha0081 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
        ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
        ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
        ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
        ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
        ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy295))
          (Class.cv (nb068AlphaDummy288))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy296))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy295)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy295)) (synC1c))
              (Class.cv (nb068AlphaDummy295))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy297 f))
          (Class.cv (nb068AlphaDummy290 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy298 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy297 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy297 f)) (synC1c))
              (Class.cv (nb068AlphaDummy297 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy295) from (by
              unfold nb068AlphaDummy295;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
          (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy297 f) from (by
              unfold nb068AlphaDummy297;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy296) from (by
                unfold nb068AlphaDummy296;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
            (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy298 f) from (by
                unfold nb068AlphaDummy298;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy321) from (by
                  unfold nb068AlphaDummy321;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0328) 0))))
              (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy322 f) from (by
                  unfold nb068AlphaDummy322;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0329 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy288) ≠ (nb068AlphaDummy319) from (by
                    unfold nb068AlphaDummy319;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0326) 0))))
                (show (nb068AlphaDummy290 f) ≠ (nb068AlphaDummy320 f) from (by
                    unfold nb068AlphaDummy320;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0327 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy288))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy290 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy302) from (by
                                  unfold nb068AlphaDummy302;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0302) 1))))
                              (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy305 f) from
                                (by
                                  unfold nb068AlphaDummy305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0303 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy301) from (by
                                    unfold nb068AlphaDummy301;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0302) 0)))) (show
                                  (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy304 f) from (by
                                    unfold nb068AlphaDummy304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0303 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from
                                    (by
                                      unfold nb068AlphaDummy299;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0300)
                                              0)))) (show
                                    (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from
                                    (by
                                      unfold nb068AlphaDummy300;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0301 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
                                  ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
                                  ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
                                  ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                                  ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                                  ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                                  ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
                                  ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                                  ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                                  ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                                  ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                                  ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                                  ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                                  ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                                  ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                                  ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0080 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                          unfold nb068AlphaDummy299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                          unfold nb068AlphaDummy300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                      ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                      ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                      ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
                      ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                      ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                      ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                      ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                      ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                      ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                      ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                      ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                      ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from
                      (by
                        unfold nb068AlphaDummy299;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                    (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                        unfold nb068AlphaDummy300;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy295) ≠ (nb068AlphaDummy299) from (by
                          unfold nb068AlphaDummy299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068AlphaDummy297 f) ≠ (nb068AlphaDummy300 f) from (by
                          unfold nb068AlphaDummy300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
                      ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
                      ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
                      ((nb068AlphaDummy321), (nb068AlphaDummy322 f)),
                      ((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                      ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                      ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                      ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                      ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                      ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                      ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                      ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                      ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0082`. -/
@[expose]
noncomputable def nb068SplitAlpha0082 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
        ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy317))
          (Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy317))
            (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy318 f))
          (Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy318 f))
            (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy288) from
                    (by
                      unfold nb068AlphaDummy288;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                  (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy290 f) from (by
                      unfold nb068AlphaDummy290;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy287) from
                      (by
                        unfold nb068AlphaDummy287;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                    (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy289 f) from (by
                        unfold nb068AlphaDummy289;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy317) from (by
                          unfold nb068AlphaDummy317;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                      (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy318 f) from (by
                          unfold nb068AlphaDummy318;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy291) from (by
                            unfold nb068AlphaDummy291;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                        (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy292 f) from (by
                            unfold nb068AlphaDummy292;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy284))).fv ∪
                      ((Class.cv (nb068AlphaDummy283))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy286 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy285 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0081 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0081 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                          ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                          ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                          ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy288) from
                      (by
                        unfold nb068AlphaDummy288;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                    (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy290 f) from (by
                        unfold nb068AlphaDummy290;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy287) from (by
                          unfold nb068AlphaDummy287;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                      (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy289 f) from (by
                          unfold nb068AlphaDummy289;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy317) from (by
                            unfold nb068AlphaDummy317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                        (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy318 f) from (by
                            unfold nb068AlphaDummy318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy291) from (by
                              unfold nb068AlphaDummy291;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                          (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy292 f) from (by
                              unfold nb068AlphaDummy292;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((synCvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy284))).fv ∪
                        ((Class.cv (nb068AlphaDummy283))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy286 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy285 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0081 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0081 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy319), (nb068AlphaDummy320 f)),
                            ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
                            ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
                            ((nb068AlphaDummy317), (nb068AlphaDummy318 f)),
                            ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
                            ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                            ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                            ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                            ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0083`. -/
@[expose]
noncomputable def nb068SplitAlpha0083 (x : Var) (y : Var) (f : Var) (dv_f_y : f ≠ y) :
    TAlphaWff
      [((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy279))
          (synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy279))
            (synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
              (Class.cv (nb068AlphaDummy002))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy280 y f))
          (synCnin (synCrn (Class.cv f)) (Class.cv y))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy280 y f))
            (synCnin (synCrn (Class.cv f)) (Class.cv y))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                          ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                          ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
          unfold nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
          unfold nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287)
        from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy293)
        from (by
          unfold nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy294 f) from (by
          unfold nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0079 x y f)))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
          unfold nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
          unfold nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287)
        from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy293)
        from (by
          unfold nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy294 f) from (by
          unfold nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0079 x y f)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb068SplitAlpha0082 x y f))))))))
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy284) from (by
                              unfold nb068AlphaDummy284;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0334) 1))))
                          (show f ≠ (nb068AlphaDummy286 f) from (by
                              unfold nb068AlphaDummy286;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0335 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy283) from (by
                                unfold nb068AlphaDummy283;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0334) 0))))
                            (show f ≠ (nb068AlphaDummy285 f) from (by
                                unfold nb068AlphaDummy285;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0335 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy281) from (by
                                  unfold nb068AlphaDummy281;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0332) 0))))
                              (show f ≠ (nb068AlphaDummy282 y f) from (by
                                  unfold nb068AlphaDummy282;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0333 y f)
                                          0)))) (TAlphaVar.there
                                (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy279) from (by
                                    unfold nb068AlphaDummy279;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0330) 0))))
                                (show f ≠ (nb068AlphaDummy280 y f) from (by
                                    unfold nb068AlphaDummy280;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0331 y f)
                                            0)))) (TAlphaVar.here _ _ _)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy281) from
                    (by
                      unfold nb068AlphaDummy281;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0338) 0))))
                  (show y ≠ (nb068AlphaDummy282 y f) from (by
                      unfold nb068AlphaDummy282;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb068_support_mem_0339 y f) 0)))) (TAlphaVar.there
                    (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy279) from (by
                        unfold nb068AlphaDummy279;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0336) 0))))
                    (show y ≠ (nb068AlphaDummy280 y f) from (by
                        unfold nb068AlphaDummy280;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0337 y f) 0))))
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                      (Ne.symm dv_f_y) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
                            ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
                            ((nb068AlphaDummy281), (nb068AlphaDummy282 y f)),
                            ((nb068AlphaDummy279), (nb068AlphaDummy280 y f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
          unfold nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
          unfold nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287)
        from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy293)
        from (by
          unfold nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy294 f) from (by
          unfold nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold
            nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold
            nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0079 x y f)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
          unfold nb068AlphaDummy288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
          unfold nb068AlphaDummy290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287)
        from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy293)
        from (by
          unfold nb068AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy294 f) from (by
          unfold nb068AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy291)
        from (by
          unfold
            nb068AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy292 f) from (by
          unfold
            nb068AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0079 x y f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb068SplitAlpha0082 x y f))))))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy284) from (by
                                unfold nb068AlphaDummy284;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0334) 1))))
                            (show f ≠ (nb068AlphaDummy286 f) from (by
                                unfold nb068AlphaDummy286;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0335 f) 1))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy283) from (by
                                  unfold nb068AlphaDummy283;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0334) 0))))
                              (show f ≠ (nb068AlphaDummy285 f) from (by
                                  unfold nb068AlphaDummy285;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0335 f) 0))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy281) from (by
                                    unfold nb068AlphaDummy281;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0332) 0))))
                                (show f ≠ (nb068AlphaDummy282 y f) from (by
                                    unfold nb068AlphaDummy282;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0333 y f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy279) from
                                    (by
                                      unfold nb068AlphaDummy279;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0330)
                                              0)))) (show f ≠ (nb068AlphaDummy280 y f) from
                                    (by
                                      unfold nb068AlphaDummy280;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0331 y f)
                                              0)))) (TAlphaVar.here _ _ _)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy281) from
                      (by
                        unfold nb068AlphaDummy281;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0338) 0))))
                    (show y ≠ (nb068AlphaDummy282 y f) from (by
                        unfold nb068AlphaDummy282;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0339 y f) 0))))
                    (TAlphaVar.there
                      (show (nb068AlphaDummy002) ≠ (nb068AlphaDummy279) from (by
                          unfold nb068AlphaDummy279;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0336) 0))))
                      (show y ≠ (nb068AlphaDummy280 y f) from (by
                          unfold nb068AlphaDummy280;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0337 y f) 0))))
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        (Ne.symm dv_f_y) (TAlphaVar.here _ _ _))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0084`. -/
@[expose]
noncomputable def nb068SplitAlpha0084 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
        ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
        ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
        ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
        ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
        ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
        ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
        ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
        ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
        ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
        ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
        ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy301))
            (synCun (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy304 f))
            (synCun (Class.cv (nb068AlphaDummy305 f))
              (Class.cv (nb068AlphaDummy306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy309) from (by
                              unfold nb068AlphaDummy309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy310 f) from (by
                              unfold nb068AlphaDummy310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy307) from (by
                                unfold nb068AlphaDummy307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy308 f) from (by
                                unfold nb068AlphaDummy308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy303), (nb068AlphaDummy306 f)),
          ((nb068AlphaDummy302), (nb068AlphaDummy305 f)),
          ((nb068AlphaDummy301), (nb068AlphaDummy304 f)),
          ((nb068AlphaDummy299), (nb068AlphaDummy300 f)),
          ((nb068AlphaDummy295), (nb068AlphaDummy297 f)),
          ((nb068AlphaDummy296), (nb068AlphaDummy298 f)),
          ((nb068AlphaDummy288), (nb068AlphaDummy290 f)),
          ((nb068AlphaDummy287), (nb068AlphaDummy289 f)),
          ((nb068AlphaDummy293), (nb068AlphaDummy294 f)),
          ((nb068AlphaDummy291), (nb068AlphaDummy292 f)),
          ((nb068AlphaDummy284), (nb068AlphaDummy286 f)),
          ((nb068AlphaDummy283), (nb068AlphaDummy285 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy313) from (by
                                unfold nb068AlphaDummy313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy314 f) from (by
                                unfold nb068AlphaDummy314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy302) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068AlphaDummy305 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy315) from (by
                                unfold nb068AlphaDummy315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy316 f) from (by
                                unfold nb068AlphaDummy316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy303) ≠ (nb068AlphaDummy311) from (by
                                  unfold nb068AlphaDummy311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068AlphaDummy306 f) ≠ (nb068AlphaDummy312 f) from
                                (by
                                  unfold nb068AlphaDummy312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
