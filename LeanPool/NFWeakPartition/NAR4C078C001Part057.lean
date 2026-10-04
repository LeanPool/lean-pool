/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block017

/-! NF weak partition development: NAR4C078C001Part057. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0026`. -/
@[expose]
noncomputable def nb078SplitAlpha0026 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
        ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
        ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
        ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
        ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy163))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy132))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy163)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy164 f))
          (synCcompl (synCphi (Class.cv (nb078AlphaDummy134 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy164 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy165) from (by
                                  unfold nb078AlphaDummy165;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0158) 0))))
                              (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy166 f) from
                                (by
                                  unfold nb078AlphaDummy166;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0159 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy163) from (by
                                    unfold nb078AlphaDummy163;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0156) 0)))) (show
                                  (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy164 f) from (by
                                    unfold nb078AlphaDummy164;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0157 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy165), (nb078AlphaDummy166 f)), ((nb078AlphaDummy163),
        (nb078AlphaDummy164 f)), ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
        ((nb078AlphaDummy131), (nb078AlphaDummy133 f)), ((nb078AlphaDummy161),
        (nb078AlphaDummy162 f)), ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy165), (nb078AlphaDummy166 f)), ((nb078AlphaDummy163),
        (nb078AlphaDummy164 f)), ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
        ((nb078AlphaDummy131), (nb078AlphaDummy133 f)), ((nb078AlphaDummy161),
        (nb078AlphaDummy162 f)), ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
                                    ((nb078AlphaDummy165), (nb078AlphaDummy166 f)),
                                    ((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
                                    ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                    ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                    ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
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
                                    ((nb078AlphaDummy165), (nb078AlphaDummy166 f)),
                                    ((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
                                    ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                    ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                    ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
                                    ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
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
                            (TAlphaVar.there
                              (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy165) from (by
                                  unfold nb078AlphaDummy165;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0158) 0))))
                              (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy166 f) from
                                (by
                                  unfold nb078AlphaDummy166;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0159 f) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy163) from (by
                                    unfold nb078AlphaDummy163;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0156) 0)))) (show
                                  (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy164 f) from (by
                                    unfold nb078AlphaDummy164;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0157 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078AlphaDummy165), (nb078AlphaDummy166 f)), ((nb078AlphaDummy163),
        (nb078AlphaDummy164 f)), ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
        ((nb078AlphaDummy131), (nb078AlphaDummy133 f)), ((nb078AlphaDummy161),
        (nb078AlphaDummy162 f)), ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy165), (nb078AlphaDummy166 f)), ((nb078AlphaDummy163),
        (nb078AlphaDummy164 f)), ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
        ((nb078AlphaDummy131), (nb078AlphaDummy133 f)), ((nb078AlphaDummy161),
        (nb078AlphaDummy162 f)), ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)), ((nb078AlphaDummy089),
        (nb078AlphaDummy091 f)), ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy204), (nb078AlphaDummy206 f)), ((nb078AlphaDummy203),
        (nb078AlphaDummy205 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
                                    ((nb078AlphaDummy165), (nb078AlphaDummy166 f)),
                                    ((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
                                    ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                    ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                    ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
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
                                    ((nb078AlphaDummy165), (nb078AlphaDummy166 f)),
                                    ((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
                                    ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
                                    ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
                                    ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
                                    ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
                                    ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
                                    ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
                                    ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
                                    ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
            ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
            ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
            ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
            ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
            ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
            ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
            ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
            ((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
            ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0027`. -/
@[expose]
noncomputable def nb078SplitAlpha0027 (x : Var) (y : Var) (f : Var) (dv_f_y : f ≠ y) :
    TAlphaWff
      [((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (synWfun (Class.cv (nb078AlphaDummy000))) (Wff.neg
          (Wff.classEq (synCdm (Class.cv (nb078AlphaDummy000)))
            (Class.cv (nb078AlphaDummy004)))))
      (Wff.imp (synWfun (Class.cv f))
        (Wff.neg (Wff.classEq (synCdm (Class.cv f)) (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0010 x y f))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                          ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                          ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                          ((nb078AlphaDummy003), x)]
                        (synCid) (nb078WppRefl0035 x y f)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0010 x y f))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
                          ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
                          ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                          ((nb078AlphaDummy003), x)]
                        (synCid) (nb078WppRefl0035 x y f)))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy015) from (by
                          unfold nb078AlphaDummy015;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0002) 0))))) (Ne.symm
                      (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy016 f) from (by
                          unfold nb078AlphaDummy016;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0003 f) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb078AlphaDummy009) ≠ (nb078AlphaDummy015) from (by
                            unfold nb078AlphaDummy015;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0000) 0))))) (Ne.symm
                        (show (nb078AlphaDummy012 f) ≠ (nb078AlphaDummy016 f) from (by
                            unfold nb078AlphaDummy016;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0001 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0011 x y f)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb078SplitAlpha0012 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb078SplitAlpha0012 x y f))))))))))))) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0013 x y f)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy011) ≠ (nb078AlphaDummy054) from (by
          unfold nb078AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 1)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy056 f) from (by
          unfold nb078AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy053)
        from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070)
                  0)))) (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy083)
        from (by
          unfold nb078AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074)
                  0)))) (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy084 f) from (by
          unfold nb078AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy057)
        from (by
          unfold nb078AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071)
                  0)))) (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy058 f) from (by
          unfold nb078AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy009))).fv ∪
        ((Class.cv (nb078AlphaDummy011))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0014 x y f)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy054) from (by
          unfold nb078AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070) 1)))) (show (nb078AlphaDummy014 f) ≠
        (nb078AlphaDummy056 f) from (by
          unfold nb078AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy053)
        from (by
          unfold nb078AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0070)
                  0)))) (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy055 f) from (by
          unfold nb078AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy083)
        from (by
          unfold nb078AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0074)
                  0)))) (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy084 f) from (by
          unfold nb078AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy057)
        from (by
          unfold nb078AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0071)
                  0)))) (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy058 f) from (by
          unfold nb078AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy009))).fv ∪
        ((Class.cv (nb078AlphaDummy011))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0014 x y f))))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb078AlphaDummy090) ≠ (nb078AlphaDummy093) from (by
                                        unfold nb078AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0082)
                                                0))))) (Ne.symm (show
                                      (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy094 f) from
                                      (by
                                        unfold nb078AlphaDummy094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0083 f)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb078AlphaDummy089) ≠ (nb078AlphaDummy093) from
                                        (by
                                          unfold nb078AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0080)
                                                  0))))) (Ne.symm (show
                                        (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy094 f)
                                        from (by
                                          unfold nb078AlphaDummy094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0081 f) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0015 x y f))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy096) from (by
          unfold
            nb078AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
          unfold
            nb078AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095)
        from (by
          unfold
            nb078AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold
            nb078AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy125)
        from (by
          unfold
            nb078AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy126 f) from (by
          unfold
            nb078AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy099)
        from (by
          unfold
            nb078AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy100 f) from (by
          unfold
            nb078AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
        ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0016 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy127), (nb078AlphaDummy128 f)), ((nb078AlphaDummy096),
        (nb078AlphaDummy098 f)), ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)), ((nb078AlphaDummy099),
        (nb078AlphaDummy100 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy090) ≠
        (nb078AlphaDummy096) from (by
          unfold
            nb078AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
          unfold
            nb078AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095)
        from (by
          unfold
            nb078AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold
            nb078AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy125)
        from (by
          unfold
            nb078AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy126 f) from (by
          unfold
            nb078AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy099)
        from (by
          unfold
            nb078AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy100 f) from (by
          unfold
            nb078AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
        ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0016 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy127), (nb078AlphaDummy128 f)), ((nb078AlphaDummy096),
        (nb078AlphaDummy098 f)), ((nb078AlphaDummy095), (nb078AlphaDummy097 f)),
        ((nb078AlphaDummy125), (nb078AlphaDummy126 f)), ((nb078AlphaDummy099),
        (nb078AlphaDummy100 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0017 x y f))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy132) from (by
          unfold
            nb078AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
          unfold
            nb078AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131)
        from (by
          unfold
            nb078AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold
            nb078AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy161)
        from (by
          unfold
            nb078AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy162 f) from (by
          unfold
            nb078AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy135)
        from (by
          unfold
            nb078AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy136 f) from (by
          unfold
            nb078AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy090))).fv ∪
        ((Class.cv (nb078AlphaDummy089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0018 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy163), (nb078AlphaDummy164 f)), ((nb078AlphaDummy132),
        (nb078AlphaDummy134 f)), ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
        ((nb078AlphaDummy161), (nb078AlphaDummy162 f)), ((nb078AlphaDummy135),
        (nb078AlphaDummy136 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy089) ≠
        (nb078AlphaDummy132) from (by
          unfold
            nb078AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
          unfold
            nb078AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131)
        from (by
          unfold
            nb078AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold
            nb078AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy161)
        from (by
          unfold
            nb078AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy162 f) from (by
          unfold
            nb078AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy135)
        from (by
          unfold
            nb078AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy136 f) from (by
          unfold
            nb078AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy090))).fv ∪
        ((Class.cv (nb078AlphaDummy089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0018 x y f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy163), (nb078AlphaDummy164 f)), ((nb078AlphaDummy132),
        (nb078AlphaDummy134 f)), ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
        ((nb078AlphaDummy161), (nb078AlphaDummy162 f)), ((nb078AlphaDummy135),
        (nb078AlphaDummy136 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y), ((nb078AlphaDummy003),
        x)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy090) from
                                    (by
                                      unfold nb078AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0170)
                                              1)))) (show f ≠ (nb078AlphaDummy092 f) from (by
                                      unfold nb078AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0171 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy000) ≠ (nb078AlphaDummy089) from (by
                                        unfold nb078AlphaDummy089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0170)
                                                0)))) (show f ≠ (nb078AlphaDummy091 f) from
                                      (by
                                        unfold nb078AlphaDummy091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy000) ≠ (nb078AlphaDummy093) from
                                        (by
                                          unfold nb078AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0168)
                                                  0)))) (show f ≠ (nb078AlphaDummy094 f) from
                                        (by
                                          unfold nb078AlphaDummy094;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0169 f) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy000) ≠
        (nb078AlphaDummy011) from (by
          unfold nb078AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0164) 2)))) (show f ≠ (nb078AlphaDummy014 f) from (by
          unfold nb078AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0166 f) 2)))) (TAlphaVar.there (show
        (nb078AlphaDummy000) ≠ (nb078AlphaDummy010) from (by
          unfold nb078AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0164) 1)))) (show f ≠ (nb078AlphaDummy013 f) from (by
          unfold nb078AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0166 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy000) ≠ (nb078AlphaDummy009) from (by
          unfold nb078AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0164) 0)))) (show f ≠ (nb078AlphaDummy012 f) from (by
          unfold nb078AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0166 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy000) ≠ (nb078AlphaDummy015) from (by
          unfold nb078AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0165) 0)))) (show f ≠ (nb078AlphaDummy016 f) from (by
          unfold nb078AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078SplitAlpha0019 x y f)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy010) ≠ (nb078AlphaDummy168) from (by
          unfold nb078AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 1)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy170 f) from (by
          unfold nb078AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy167)
        from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200)
                  0)))) (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy197)
        from (by
          unfold nb078AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204)
                  0)))) (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy198 f) from (by
          unfold nb078AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy171)
        from (by
          unfold nb078AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201)
                  0)))) (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy172 f) from (by
          unfold nb078AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy011))).fv ∪
        ((Class.cv (nb078AlphaDummy010))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0020 x y f)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy168) from (by
          unfold nb078AlphaDummy168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200) 1)))) (show (nb078AlphaDummy013 f) ≠
        (nb078AlphaDummy170 f) from (by
          unfold nb078AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy167)
        from (by
          unfold nb078AlphaDummy167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0200)
                  0)))) (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy169 f) from (by
          unfold nb078AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy197)
        from (by
          unfold nb078AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0204)
                  0)))) (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy198 f) from (by
          unfold nb078AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy010) ≠ (nb078AlphaDummy171)
        from (by
          unfold nb078AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0201)
                  0)))) (show (nb078AlphaDummy013 f) ≠ (nb078AlphaDummy172 f) from (by
          unfold nb078AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv ∪ ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy011))).fv ∪
        ((Class.cv (nb078AlphaDummy010))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078SplitAlpha0020 x y f))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.there
                        (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy011) from (by
                            unfold nb078AlphaDummy011;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0164) 2))))
                        (show f ≠ (nb078AlphaDummy014 f) from (by
                            unfold nb078AlphaDummy014;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0166 f) 2))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy010) from (by
                              unfold nb078AlphaDummy010;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0164) 1))))
                          (show f ≠ (nb078AlphaDummy013 f) from (by
                              unfold nb078AlphaDummy013;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0166 f) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy009) from (by
                                unfold nb078AlphaDummy009;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0164) 0))))
                            (show f ≠ (nb078AlphaDummy012 f) from (by
                                unfold nb078AlphaDummy012;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0166 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy015) from (by
                                  unfold nb078AlphaDummy015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0165) 0))))
                              (show f ≠ (nb078AlphaDummy016 f) from (by
                                  unfold nb078AlphaDummy016;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0167 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy204), (nb078AlphaDummy206 f)),
                    ((nb078AlphaDummy203), (nb078AlphaDummy205 f)),
                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078SplitAlpha0022 x y f))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                                (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy093) from (by
                                    unfold nb078AlphaDummy093;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0082) 0)))))
                              (Ne.symm (show
                                  (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy094 f) from (by
                                    unfold nb078AlphaDummy094;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0083 f)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy093) from
                                    (by
                                      unfold nb078AlphaDummy093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0080)
                                              0))))) (Ne.symm (show
                                    (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy094 f) from
                                    (by
                                      unfold nb078AlphaDummy094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0081 f)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078SplitAlpha0023 x y f)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy096) from (by
          unfold nb078AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
          unfold nb078AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095)
        from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy125)
        from (by
          unfold
            nb078AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy126 f) from (by
          unfold
            nb078AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy099)
        from (by
          unfold
            nb078AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy100 f) from (by
          unfold
            nb078AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
        ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0024 x y f))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy096) from (by
          unfold nb078AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  1)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy098 f) from (by
          unfold nb078AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy095)
        from (by
          unfold nb078AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0112)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy097 f) from (by
          unfold nb078AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy125)
        from (by
          unfold
            nb078AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0116)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy126 f) from (by
          unfold
            nb078AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy090) ≠ (nb078AlphaDummy099)
        from (by
          unfold
            nb078AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0113)
                  0)))) (show (nb078AlphaDummy092 f) ≠ (nb078AlphaDummy100 f) from (by
          unfold
            nb078AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy089))).fv ∪
        ((Class.cv (nb078AlphaDummy090))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0024 x y f))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078SplitAlpha0025 x y f)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy132) from (by
          unfold nb078AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
          unfold nb078AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131)
        from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy161)
        from (by
          unfold
            nb078AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy162 f) from (by
          unfold
            nb078AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy135)
        from (by
          unfold
            nb078AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy136 f) from (by
          unfold
            nb078AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy090))).fv ∪
        ((Class.cv (nb078AlphaDummy089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0026 x y f))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy132) from (by
          unfold nb078AlphaDummy132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  1)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy134 f) from (by
          unfold nb078AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy131)
        from (by
          unfold nb078AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0150)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy133 f) from (by
          unfold nb078AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy161)
        from (by
          unfold
            nb078AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0154)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy162 f) from (by
          unfold
            nb078AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy089) ≠ (nb078AlphaDummy135)
        from (by
          unfold
            nb078AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0151)
                  0)))) (show (nb078AlphaDummy091 f) ≠ (nb078AlphaDummy136 f) from (by
          unfold
            nb078AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy090))).fv ∪
        ((Class.cv (nb078AlphaDummy089))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078SplitAlpha0026 x y f)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy090) from (by
                                  unfold nb078AlphaDummy090;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0170) 1))))
                              (show f ≠ (nb078AlphaDummy092 f) from (by
                                  unfold nb078AlphaDummy092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0171 f) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy089) from (by
                                    unfold nb078AlphaDummy089;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0170) 0))))
                                (show f ≠ (nb078AlphaDummy091 f) from (by
                                    unfold nb078AlphaDummy091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0171 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy000) ≠ (nb078AlphaDummy093) from
                                    (by
                                      unfold nb078AlphaDummy093;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0168)
                                              0)))) (show f ≠ (nb078AlphaDummy094 f) from (by
                                      unfold nb078AlphaDummy094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0169 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy000) ≠ (nb078AlphaDummy204) from (by
                                        unfold nb078AlphaDummy204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0248)
                                                1)))) (show f ≠ (nb078AlphaDummy206 f) from
                                      (by
                                        unfold nb078AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0249 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy000) ≠ (nb078AlphaDummy203) from
                                        (by
                                          unfold nb078AlphaDummy203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0248)
                                                  0)))) (show f ≠ (nb078AlphaDummy205 f) from
                                        (by
                                          unfold nb078AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0249 f) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_f_y) (TAlphaVar.here _ _ _))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
