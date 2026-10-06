/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part048`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0128`. -/
@[expose]
noncomputable def nb068SplitAlpha0128 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0129`. -/
@[expose]
noncomputable def nb068SplitAlpha0129 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy140))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
          (Class.cv (nb068AlphaDummy139))))
      (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
          (Class.cv (nb068AlphaDummy141 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                              unfold nb068AlphaDummy146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                          (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from (by
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
                                      (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                            (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                                unfold nb068AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                                  unfold nb068AlphaDummy143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from
                                (by
                                  unfold nb068AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                              ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                              ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                              ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                              ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                              ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                              ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                              ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                              ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                              ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0128 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                      unfold nb068AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                      unfold nb068AlphaDummy144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                    unfold nb068AlphaDummy143;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                    unfold nb068AlphaDummy144;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
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
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0130`. -/
@[expose]
noncomputable def nb068SplitAlpha0130 (x : Var) (y : Var) (f : Var) :
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
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part049`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0131`. -/
@[expose]
noncomputable def nb068SplitAlpha0131 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
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
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy143))
              (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy143)) (Class.cv (nb068AlphaDummy139)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy144 f))
              (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy144 f))
            (Class.cv (nb068AlphaDummy141 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                          unfold nb068AlphaDummy146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from (by
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
                                  (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                        (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                            unfold nb068AlphaDummy148;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
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
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
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
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068SplitAlpha0130 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                  unfold nb068AlphaDummy143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                  unfold nb068AlphaDummy144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
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
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                unfold nb068AlphaDummy143;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
            (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                unfold nb068AlphaDummy144;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                  unfold nb068AlphaDummy143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                  unfold nb068AlphaDummy144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
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
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0132`. -/
@[expose]
noncomputable def nb068SplitAlpha0132 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy132))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb068SplitAlpha0131 x y f)))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy132))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb068SplitAlpha0131 x y f)))))))))))
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
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb068SplitAlpha0131 x y f)))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb068SplitAlpha0131 x y f)))))))))))
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
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                            ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0133`. -/
@[expose]
noncomputable def nb068SplitAlpha0133 (x : Var) (y : Var) (f : Var) :
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
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0134`. -/
@[expose]
noncomputable def nb068SplitAlpha0134 (x : Var) (y : Var) (f : Var) :
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
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy176))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
          (Class.cv (nb068AlphaDummy175))))
      (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
          (Class.cv (nb068AlphaDummy177 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                              unfold nb068AlphaDummy182;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                          (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from (by
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
                                      (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                            (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                                unfold nb068AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                                  unfold nb068AlphaDummy179;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                (by
                                  unfold nb068AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
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
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0133 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                      unfold nb068AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                  (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                      unfold nb068AlphaDummy180;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
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
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                    unfold nb068AlphaDummy179;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                    unfold nb068AlphaDummy180;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
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
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
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
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                  ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part050`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0135`. -/
@[expose]
noncomputable def nb068SplitAlpha0135 (x : Var) (y : Var) (f : Var) :
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
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0136`. -/
@[expose]
noncomputable def nb068SplitAlpha0136 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
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
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy179))
              (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy179)) (Class.cv (nb068AlphaDummy175)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy180 f))
              (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy180 f))
            (Class.cv (nb068AlphaDummy177 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                          unfold nb068AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from (by
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
                                  (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                        (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                            unfold nb068AlphaDummy184;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
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
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
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
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                          ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068SplitAlpha0135 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                  unfold nb068AlphaDummy179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                  unfold nb068AlphaDummy180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
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
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                unfold nb068AlphaDummy179;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
            (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                unfold nb068AlphaDummy180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                  unfold nb068AlphaDummy179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                  unfold nb068AlphaDummy180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
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
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
              ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0137`. -/
@[expose]
noncomputable def nb068SplitAlpha0137 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.neg (Wff.all (nb068AlphaDummy168) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb068AlphaDummy168))
                (Class.cv (nb068AlphaDummy125)))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168))) (synCsn (synC0c))))))))
      (Wff.neg (Wff.all (nb068AlphaDummy170 f) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb068AlphaDummy170 f))
                (Class.cv (nb068AlphaDummy127 f)))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from (by
                unfold nb068AlphaDummy168;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
            (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                unfold nb068AlphaDummy170;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
                  unfold nb068AlphaDummy167;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
              (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                  unfold nb068AlphaDummy169;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                    unfold nb068AlphaDummy197;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                    unfold nb068AlphaDummy198;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from
                    (by
                      unfold nb068AlphaDummy171;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                  (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                      unfold nb068AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                      (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy126))).fv ∪
                ((Class.cv (nb068AlphaDummy125))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
                                        unfold nb068AlphaDummy175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068AlphaDummy170 f) ≠
                                        (nb068AlphaDummy177 f) from (by
                                        unfold nb068AlphaDummy177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from
                                        (by
                                          unfold nb068AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
                                          unfold nb068AlphaDummy178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068SplitAlpha0136 x y f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
                                        unfold nb068AlphaDummy175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068AlphaDummy170 f) ≠
                                        (nb068AlphaDummy177 f) from (by
                                        unfold nb068AlphaDummy177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from
                                        (by
                                          unfold nb068AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
                                          unfold nb068AlphaDummy178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068SplitAlpha0136 x y f)))))))))))
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
                    ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                    ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                    ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                    ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                    ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
                    ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
                    ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                    ((nb068AlphaDummy001), x),
                    ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0138`. -/
@[expose]
noncomputable def nb068SplitAlpha0138 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classMem
        (synCop (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy125)))
        (Class.cv (nb068AlphaDummy000)))
      (Wff.classMem (synCop (Class.cv (nb068AlphaDummy128 f))
          (Class.cv (nb068AlphaDummy127 f))) (Class.cv f)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                    unfold nb068AlphaDummy168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
                                    unfold nb068AlphaDummy170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                    (by
                                      unfold nb068AlphaDummy167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from
                                    (by
                                      unfold nb068AlphaDummy169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy173) from (by
                                        unfold nb068AlphaDummy173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy174 f) from (by
                                        unfold nb068AlphaDummy174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from
                                        (by
                                          unfold nb068AlphaDummy171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
                                          unfold nb068AlphaDummy172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy126))).fv ∪
                                    ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                    ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068SplitAlpha0134 x y f)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                    unfold nb068AlphaDummy168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
                                    unfold nb068AlphaDummy170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                    (by
                                      unfold nb068AlphaDummy167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from
                                    (by
                                      unfold nb068AlphaDummy169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy173) from (by
                                        unfold nb068AlphaDummy173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy174 f) from (by
                                        unfold nb068AlphaDummy174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from
                                        (by
                                          unfold nb068AlphaDummy171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
                                          unfold nb068AlphaDummy172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy126))).fv ∪
                                    ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                    ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068SplitAlpha0134 x y f)))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (nb068SplitAlpha0137 x y f)))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (nb068SplitAlpha0137 x y f)))))))))) (TAlphaClass.cv
      (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy126) from (by
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
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
            (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy329) from (by
                  unfold nb068AlphaDummy329;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 2))))
              (show f ≠ (nb068AlphaDummy332 f) from (by
                  unfold nb068AlphaDummy332;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0506 f) 2))))
              (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy328) from (by
                    unfold nb068AlphaDummy328;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 1))))
                (show f ≠ (nb068AlphaDummy331 f) from (by
                    unfold nb068AlphaDummy331;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0506 f) 1))))
                (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy327) from
                    (by
                      unfold nb068AlphaDummy327;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 0))))
                  (show f ≠ (nb068AlphaDummy330 f) from (by
                      unfold nb068AlphaDummy330;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0506 f) 0))))
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy333) from
                      (by
                        unfold nb068AlphaDummy333;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0505) 0))))
                    (show f ≠ (nb068AlphaDummy334 f) from (by
                        unfold nb068AlphaDummy334;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0507 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy325) from (by
                          unfold nb068AlphaDummy325;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0502) 0))))
                      (show f ≠ (nb068AlphaDummy326 f) from (by
                          unfold nb068AlphaDummy326;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0503 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy323) from (by
                            unfold nb068AlphaDummy323;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0500) 0))))
                        (show f ≠ (nb068AlphaDummy324 f) from (by
                            unfold nb068AlphaDummy324;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0501 f) 0))))
                        (TAlphaVar.here _ _ _))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0139`. -/
@[expose]
noncomputable def nb068SplitAlpha0139 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.all (nb068AlphaDummy126) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb068AlphaDummy129))
              (synCop (Class.cv (nb068AlphaDummy125)) (Class.cv (nb068AlphaDummy126))))
            (synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy125))))))
      (Wff.all (nb068AlphaDummy128 f) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb068AlphaDummy130 f))
              (synCop (Class.cv (nb068AlphaDummy127 f))
                (Class.cv (nb068AlphaDummy128 f))))
            (synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
              (Class.cv (nb068AlphaDummy127 f)))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (Ne.symm
                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy129) from (by
                    unfold nb068AlphaDummy129;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0)))))
              (Ne.symm (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy130 f) from (by
                    unfold nb068AlphaDummy130;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
              (TAlphaVar.there (Ne.symm
                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy129) from (by
                      unfold nb068AlphaDummy129;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
                (Ne.symm (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy130 f) from (by
                      unfold nb068AlphaDummy130;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                        (by
                                          unfold nb068AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy134 f) from (by
                                          unfold nb068AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from (by
          unfold nb068AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
          unfold nb068AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy135) from (by
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
                                      (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy125))).fv ∪
        ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy127 f))).fv ∪
        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068SplitAlpha0129 x y f)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                        (by
                                          unfold nb068AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy134 f) from (by
                                          unfold nb068AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from (by
          unfold nb068AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
          unfold nb068AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy135) from (by
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
                                      (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy125))).fv ∪
        ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy127 f))).fv ∪
        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068SplitAlpha0129 x y f)))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0132 x y f)))))))))
        (nb068SplitAlpha0138 x y f))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0140`. -/
@[expose]
noncomputable def nb068SplitAlpha0140 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy327))
          (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
          (Class.cv (nb068AlphaDummy329))) (Wff.neg
          (synWbr (Class.cv (nb068AlphaDummy329))
            (synCcnv (Class.cv (nb068AlphaDummy000))) (Class.cv (nb068AlphaDummy328)))))
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy330 f)) (synCcnv (synCcnv (Class.cv f)))
          (Class.cv (nb068AlphaDummy332 f))) (Wff.neg
          (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy331 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy372) from
                                    (by
                                      unfold nb068AlphaDummy372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0382)
                                              1)))) (show
                                    (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy374 f) from
                                    (by
                                      unfold nb068AlphaDummy374;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0384 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy327) ≠ (nb068AlphaDummy371) from (by
                                        unfold nb068AlphaDummy371;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0382)
                                                0)))) (show (nb068AlphaDummy330 f) ≠
                                        (nb068AlphaDummy373 f) from (by
                                        unfold nb068AlphaDummy373;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0384 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy327) ≠ (nb068AlphaDummy377) from
                                        (by
                                          unfold nb068AlphaDummy377;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0386)
                                                  0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy378 f) from (by
                                          unfold nb068AlphaDummy378;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0387 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy327) ≠
        (nb068AlphaDummy375) from (by
          unfold nb068AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0383) 0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy376 f) from (by
          unfold nb068AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0385 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy327))).fv ∪
                                      ((Class.cv (nb068AlphaDummy329))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy330 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy332 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0095 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy372) from
                                    (by
                                      unfold nb068AlphaDummy372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0382)
                                              1)))) (show
                                    (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy374 f) from
                                    (by
                                      unfold nb068AlphaDummy374;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0384 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy327) ≠ (nb068AlphaDummy371) from (by
                                        unfold nb068AlphaDummy371;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0382)
                                                0)))) (show (nb068AlphaDummy330 f) ≠
                                        (nb068AlphaDummy373 f) from (by
                                        unfold nb068AlphaDummy373;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0384 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy327) ≠ (nb068AlphaDummy377) from
                                        (by
                                          unfold nb068AlphaDummy377;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0386)
                                                  0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy378 f) from (by
                                          unfold nb068AlphaDummy378;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0387 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy327) ≠
        (nb068AlphaDummy375) from (by
          unfold nb068AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0383) 0)))) (show (nb068AlphaDummy330 f) ≠
        (nb068AlphaDummy376 f) from (by
          unfold nb068AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0385 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb068AlphaDummy000))))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy327))).fv ∪
                                      ((Class.cv (nb068AlphaDummy329))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy330 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy332 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0095 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0098 x y f))))))))
      (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0122 x y f))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy329) ≠ (nb068AlphaDummy486) from (by
                                        unfold nb068AlphaDummy486;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0512)
                                                1)))) (show (nb068AlphaDummy332 f) ≠
                                        (nb068AlphaDummy488 f) from (by
                                        unfold nb068AlphaDummy488;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0514 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy329) ≠ (nb068AlphaDummy485) from
                                        (by
                                          unfold nb068AlphaDummy485;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0512)
                                                  0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy487 f) from (by
                                          unfold nb068AlphaDummy487;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0514 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy329) ≠
        (nb068AlphaDummy491) from (by
          unfold nb068AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0516) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy492 f) from (by
          unfold nb068AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0517 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy329) ≠ (nb068AlphaDummy489) from (by
          unfold nb068AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0513) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy490 f) from (by
          unfold nb068AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0515 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy329))).fv ∪
                                        ((Class.cv (nb068AlphaDummy328))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy332 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy331 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0124 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy329) ≠ (nb068AlphaDummy486) from (by
                                        unfold nb068AlphaDummy486;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0512)
                                                1)))) (show (nb068AlphaDummy332 f) ≠
                                        (nb068AlphaDummy488 f) from (by
                                        unfold nb068AlphaDummy488;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0514 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy329) ≠ (nb068AlphaDummy485) from
                                        (by
                                          unfold nb068AlphaDummy485;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0512)
                                                  0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy487 f) from (by
                                          unfold nb068AlphaDummy487;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0514 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy329) ≠
        (nb068AlphaDummy491) from (by
          unfold nb068AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0516) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy492 f) from (by
          unfold nb068AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0517 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy329) ≠ (nb068AlphaDummy489) from (by
          unfold nb068AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0513) 0)))) (show (nb068AlphaDummy332 f) ≠
        (nb068AlphaDummy490 f) from (by
          unfold nb068AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0515 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy329))).fv ∪
                                        ((Class.cv (nb068AlphaDummy328))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy332 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy331 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0124 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0127 x y f))))))))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0139 x y f)))))))

theorem nb068_wpp_notmem_1322 : (nb068AlphaDummy325) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy325, fv_syn_cid] using (nb068_compact_fv_empty_0272)

theorem nb068_wpp_notmem_1323 (f : Var) : (nb068AlphaDummy326 f) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy326, fv_syn_cid] using (nb068_compact_fv_empty_0273 f)

theorem nb068_wpp_notmem_1324 : (nb068AlphaDummy323) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy323, fv_syn_cid] using (nb068_compact_fv_empty_0274)

theorem nb068_wpp_notmem_1325 (f : Var) : (nb068AlphaDummy324 f) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy324, fv_syn_cid] using (nb068_compact_fv_empty_0275 f)

theorem nb068_compact_envfresh_0179 (x : Var) (y : Var) (f : Var) :
    TEnvFresh
      [((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb068AlphaDummy325) (nb068AlphaDummy326 f)
      (nb068_wpp_notmem_1322) (nb068_wpp_notmem_1323 f)
      (TEnvFresh.consFresh (nb068AlphaDummy323) (nb068AlphaDummy324 f)
        (nb068_wpp_notmem_1324) (nb068_wpp_notmem_1325 f)
        (TEnvFresh.consFresh (nb068AlphaDummy000) f (nb068_wpp_notmem_0600)
          (nb068_wpp_notmem_0601 f)
          (TEnvFresh.consFresh (nb068AlphaDummy002) y (nb068_wpp_notmem_0602)
            (nb068_wpp_notmem_0603 y)
            (TEnvFresh.consFresh (nb068AlphaDummy001) x (nb068_wpp_notmem_0604)
              (nb068_wpp_notmem_0605 x)
              (TEnvFresh.consFresh (nb068AlphaDummy003) (nb068AlphaDummy004 x y f)
                (nb068_wpp_notmem_0606) (nb068_wpp_notmem_0607 x y f)
                (TEnvFresh.nil ((synCid)).fv)))))))

/-- Checked nominal proof certificate identified upstream as `nb068_wpp_refl_0179`. -/
@[expose]
noncomputable def nb068WppRefl0179 (x : Var) (y : Var) (f : Var) :
    TReflOn
      [((nb068AlphaDummy325), (nb068AlphaDummy326 f)),
        ((nb068AlphaDummy323), (nb068AlphaDummy324 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0179 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
