/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part048`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0017`. -/
@[expose]
noncomputable def nb078SplitAlpha0017 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy137), (nb078AlphaDummy138 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
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
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
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
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
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
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
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
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
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
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part049`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0018`. -/
@[expose]
noncomputable def nb078SplitAlpha0018 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy165), (nb078AlphaDummy166 f)),
        ((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
        ((nb078AlphaDummy132), (nb078AlphaDummy134 f)),
        ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
        ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)),
        ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy165))
          (synCphi (Class.cv (nb078AlphaDummy132)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy165))
            (synCphi (Class.cv (nb078AlphaDummy132))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy166 f))
          (synCphi (Class.cv (nb078AlphaDummy134 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy166 f))
            (synCphi (Class.cv (nb078AlphaDummy134 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy139) from
                    (by
                      unfold nb078AlphaDummy139;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                  (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy141 f) from (by
                      unfold nb078AlphaDummy141;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0129 f) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy140) from
                      (by
                        unfold nb078AlphaDummy140;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 1))))
                    (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy142 f) from (by
                        unfold nb078AlphaDummy142;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0129 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy165) from (by
                          unfold nb078AlphaDummy165;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0158) 0))))
                      (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy166 f) from (by
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
                                  (mem_lt_freshVar (nb078_support_mem_0156) 0))))
                        (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy164 f) from (by
                            unfold nb078AlphaDummy164;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy132))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy134 f))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy139) ≠ (nb078AlphaDummy146) from (by
                                        unfold nb078AlphaDummy146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0132)
                                                1)))) (show (nb078AlphaDummy141 f) ≠
                                        (nb078AlphaDummy149 f) from (by
                                        unfold nb078AlphaDummy149;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0133 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy139) ≠ (nb078AlphaDummy145) from
                                        (by
                                          unfold nb078AlphaDummy145;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0132)
                                                  0)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy148 f) from (by
                                          unfold nb078AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0133 f) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy139) ≠
        (nb078AlphaDummy143) from (by
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
                  (nb078_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy147),
        (nb078AlphaDummy150 f)), ((nb078AlphaDummy146), (nb078AlphaDummy149 f)),
                                        ((nb078AlphaDummy145), (nb078AlphaDummy148 f)),
                                        ((nb078AlphaDummy143), (nb078AlphaDummy144 f)),
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
                                        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                        ((nb078AlphaDummy000), f),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy146) ≠
        (nb078AlphaDummy153) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy147), (nb078AlphaDummy150 f)),
        ((nb078AlphaDummy146), (nb078AlphaDummy149 f)), ((nb078AlphaDummy145),
        (nb078AlphaDummy148 f)), ((nb078AlphaDummy143), (nb078AlphaDummy144 f)),
        ((nb078AlphaDummy139), (nb078AlphaDummy141 f)), ((nb078AlphaDummy140),
        (nb078AlphaDummy142 f)), ((nb078AlphaDummy165), (nb078AlphaDummy166 f)),
        ((nb078AlphaDummy163), (nb078AlphaDummy164 f)), ((nb078AlphaDummy132),
        (nb078AlphaDummy134 f)), ((nb078AlphaDummy131), (nb078AlphaDummy133 f)),
        ((nb078AlphaDummy161), (nb078AlphaDummy162 f)), ((nb078AlphaDummy135),
        (nb078AlphaDummy136 f)), ((nb078AlphaDummy090), (nb078AlphaDummy092 f)),
        ((nb078AlphaDummy089), (nb078AlphaDummy091 f)), ((nb078AlphaDummy093),
        (nb078AlphaDummy094 f)), ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)), ((nb078AlphaDummy009),
        (nb078AlphaDummy012 f)), ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy146) ≠
        (nb078AlphaDummy157) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                unfold nb078AlphaDummy143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                            (show (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from (by
                                unfold nb078AlphaDummy144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
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
                            ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                            ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                            ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                            ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                              unfold nb078AlphaDummy143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                          (show (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from (by
                              unfold nb078AlphaDummy144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                unfold nb078AlphaDummy143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                            (show (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from (by
                                unfold nb078AlphaDummy144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
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
                            ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                            ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                            ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                            ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                            ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy132) ≠ (nb078AlphaDummy139) from (by
                        unfold nb078AlphaDummy139;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                    (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy141 f) from (by
                        unfold nb078AlphaDummy141;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0129 f) 0)))) (TAlphaVar.there
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
                        (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy166 f) from (by
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
                                    (mem_lt_freshVar (nb078_support_mem_0156) 0))))
                          (show (nb078AlphaDummy134 f) ≠ (nb078AlphaDummy164 f) from (by
                              unfold nb078AlphaDummy164;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy132))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy134 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy139) ≠ (nb078AlphaDummy146) from
                                        (by
                                          unfold nb078AlphaDummy146;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0132)
                                                  1)))) (show (nb078AlphaDummy141 f) ≠
        (nb078AlphaDummy149 f) from (by
                                          unfold nb078AlphaDummy149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0133 f) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy139) ≠
        (nb078AlphaDummy145) from (by
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
                  (nb078_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy147),
        (nb078AlphaDummy150 f)), ((nb078AlphaDummy146), (nb078AlphaDummy149 f)),
        ((nb078AlphaDummy145), (nb078AlphaDummy148 f)), ((nb078AlphaDummy143),
        (nb078AlphaDummy144 f)), ((nb078AlphaDummy139), (nb078AlphaDummy141 f)),
        ((nb078AlphaDummy140), (nb078AlphaDummy142 f)), ((nb078AlphaDummy165),
        (nb078AlphaDummy166 f)), ((nb078AlphaDummy163), (nb078AlphaDummy164 f)),
        ((nb078AlphaDummy132), (nb078AlphaDummy134 f)), ((nb078AlphaDummy131),
        (nb078AlphaDummy133 f)), ((nb078AlphaDummy161), (nb078AlphaDummy162 f)),
        ((nb078AlphaDummy135), (nb078AlphaDummy136 f)), ((nb078AlphaDummy090),
        (nb078AlphaDummy092 f)), ((nb078AlphaDummy089), (nb078AlphaDummy091 f)),
        ((nb078AlphaDummy093), (nb078AlphaDummy094 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy146) ≠
        (nb078AlphaDummy153) from (by
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
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
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)), ((nb078AlphaDummy010),
        (nb078AlphaDummy013 f)), ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy139))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy139))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy146) ≠
        (nb078AlphaDummy157) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                  unfold nb078AlphaDummy143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                              (show (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from
                                (by
                                  unfold nb078AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
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
                              ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                              ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                              ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                              ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                              ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                unfold nb078AlphaDummy143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                            (show (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from (by
                                unfold nb078AlphaDummy144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy139) ≠ (nb078AlphaDummy143) from (by
                                  unfold nb078AlphaDummy143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                              (show (nb078AlphaDummy141 f) ≠ (nb078AlphaDummy144 f) from
                                (by
                                  unfold nb078AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
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
                              ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                              ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                              ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                              ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                              ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part050`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0019`. -/
@[expose]
noncomputable def nb078SplitAlpha0019 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
        ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
        ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
        ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
        ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy173))
          (Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy173)) (Class.cab (nb078AlphaDummy167)
              (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
                (Wff.classEq (Class.cv (nb078AlphaDummy167))
                  (synCphi (Class.cv (nb078AlphaDummy168)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy174 f))
          (Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy174 f))
            (Class.cab (nb078AlphaDummy169 f)
              (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
                (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                  (synCphi (Class.cv (nb078AlphaDummy170 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy168) from
                    (by
                      unfold nb078AlphaDummy168;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
                  (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy170 f) from (by
                      unfold nb078AlphaDummy170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy167) from
                      (by
                        unfold nb078AlphaDummy167;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))))
                    (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy169 f) from (by
                        unfold nb078AlphaDummy169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0174 f) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy173) from (by
                          unfold nb078AlphaDummy173;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0176) 0))))
                      (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy174 f) from (by
                          unfold nb078AlphaDummy174;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0177 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy171) from (by
                            unfold nb078AlphaDummy171;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0173) 0))))
                        (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy172 f) from (by
                            unfold nb078AlphaDummy172;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0175 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy011))).fv ∪
                      ((Class.cv (nb078AlphaDummy010))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy014 f))).fv ∪
                      ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy175) from (by
                              unfold nb078AlphaDummy175;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0178) 0))))
                          (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy177 f) from (by
                              unfold nb078AlphaDummy177;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy176) from (by
                                unfold nb078AlphaDummy176;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0178) 1))))
                            (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy178 f) from (by
                                unfold nb078AlphaDummy178;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0179 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy168))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy170 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy182) from (by
          unfold nb078AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 1)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy185 f) from (by
          unfold nb078AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy181) from (by
          unfold nb078AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy184 f) from (by
          unfold nb078AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
          unfold nb078AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180) 0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
          unfold nb078AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy168), (nb078AlphaDummy170 f)), ((nb078AlphaDummy167),
        (nb078AlphaDummy169 f)), ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
        ((nb078AlphaDummy171), (nb078AlphaDummy172 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy168), (nb078AlphaDummy170 f)), ((nb078AlphaDummy167),
        (nb078AlphaDummy169 f)), ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
        ((nb078AlphaDummy171), (nb078AlphaDummy172 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy177
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193) from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193)
        from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠
        (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
                                        unfold nb078AlphaDummy179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078AlphaDummy177 f) ≠
                                        (nb078AlphaDummy180 f) from (by
                                        unfold nb078AlphaDummy180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                    ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                    ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                    ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                    ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                    ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
                                    ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                    (by
                                      unfold nb078AlphaDummy179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0180)
                                              0)))) (show
                                    (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from
                                    (by
                                      unfold nb078AlphaDummy180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
                                        unfold nb078AlphaDummy179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078AlphaDummy177 f) ≠
                                        (nb078AlphaDummy180 f) from (by
                                        unfold nb078AlphaDummy180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                    ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                    ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                    ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                    ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                    ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
                                    ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                    ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                    ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                    ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                    ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                    ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy168) from
                      (by
                        unfold nb078AlphaDummy168;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
                    (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy170 f) from (by
                        unfold nb078AlphaDummy170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0174 f) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy167) from (by
                          unfold nb078AlphaDummy167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0172) 0))))
                      (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy169 f) from (by
                          unfold nb078AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0174 f) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy173) from (by
                            unfold nb078AlphaDummy173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0176) 0))))
                        (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy174 f) from (by
                            unfold nb078AlphaDummy174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0177 f) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy011) ≠ (nb078AlphaDummy171) from (by
                              unfold nb078AlphaDummy171;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0173) 0))))
                          (show (nb078AlphaDummy014 f) ≠ (nb078AlphaDummy172 f) from (by
                              unfold nb078AlphaDummy172;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0175 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy011))).fv ∪
                        ((Class.cv (nb078AlphaDummy010))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy014 f))).fv ∪
                        ((Class.cv (nb078AlphaDummy013 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy175) from (by
                                unfold nb078AlphaDummy175;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0178) 0))))
                            (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy177 f) from (by
                                unfold nb078AlphaDummy177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0179 f) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy168) ≠ (nb078AlphaDummy176) from (by
                                  unfold nb078AlphaDummy176;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0178) 1))))
                              (show (nb078AlphaDummy170 f) ≠ (nb078AlphaDummy178 f) from
                                (by
                                  unfold nb078AlphaDummy178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0179 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy168))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy170 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy182) from (by
          unfold nb078AlphaDummy182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 1)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy185 f) from (by
          unfold nb078AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy175) ≠ (nb078AlphaDummy181) from (by
          unfold nb078AlphaDummy181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy184 f) from (by
          unfold nb078AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy175) ≠ (nb078AlphaDummy179)
        from (by
          unfold nb078AlphaDummy179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180)
                  0)))) (show (nb078AlphaDummy177 f) ≠ (nb078AlphaDummy180 f) from (by
          unfold nb078AlphaDummy180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy168), (nb078AlphaDummy170 f)), ((nb078AlphaDummy167),
        (nb078AlphaDummy169 f)), ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
        ((nb078AlphaDummy171), (nb078AlphaDummy172 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy189) from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy189)
        from (by
          unfold
            nb078AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy190 f) from (by
          unfold
            nb078AlphaDummy190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy187)
        from (by
          unfold
            nb078AlphaDummy187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy188 f) from (by
          unfold
            nb078AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy183), (nb078AlphaDummy186 f)), ((nb078AlphaDummy182),
        (nb078AlphaDummy185 f)), ((nb078AlphaDummy181), (nb078AlphaDummy184 f)),
        ((nb078AlphaDummy179), (nb078AlphaDummy180 f)), ((nb078AlphaDummy175),
        (nb078AlphaDummy177 f)), ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
        ((nb078AlphaDummy168), (nb078AlphaDummy170 f)), ((nb078AlphaDummy167),
        (nb078AlphaDummy169 f)), ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
        ((nb078AlphaDummy171), (nb078AlphaDummy172 f)), ((nb078AlphaDummy011),
        (nb078AlphaDummy014 f)), ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
        ((nb078AlphaDummy009), (nb078AlphaDummy012 f)), ((nb078AlphaDummy015),
        (nb078AlphaDummy016 f)), ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy175))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy177
        f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193) from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy193)
        from (by
          unfold
            nb078AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy194 f) from (by
          unfold
            nb078AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy182) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078AlphaDummy185 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy183) ≠
        (nb078AlphaDummy195) from (by
          unfold
            nb078AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy196 f) from (by
          unfold
            nb078AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy183) ≠ (nb078AlphaDummy191)
        from (by
          unfold
            nb078AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078AlphaDummy186 f) ≠ (nb078AlphaDummy192 f) from (by
          unfold
            nb078AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                        (by
                                          unfold nb078AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
                                          unfold nb078AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                      ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                      ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                      ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                      ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                      ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
                                      ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from (by
                                        unfold nb078AlphaDummy179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078AlphaDummy177 f) ≠
                                        (nb078AlphaDummy180 f) from (by
                                        unfold nb078AlphaDummy180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy175) ≠ (nb078AlphaDummy179) from
                                        (by
                                          unfold nb078AlphaDummy179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078AlphaDummy177 f) ≠
        (nb078AlphaDummy180 f) from (by
                                          unfold nb078AlphaDummy180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy179), (nb078AlphaDummy180 f)),
                                      ((nb078AlphaDummy175), (nb078AlphaDummy177 f)),
                                      ((nb078AlphaDummy176), (nb078AlphaDummy178 f)),
                                      ((nb078AlphaDummy168), (nb078AlphaDummy170 f)),
                                      ((nb078AlphaDummy167), (nb078AlphaDummy169 f)),
                                      ((nb078AlphaDummy173), (nb078AlphaDummy174 f)),
                                      ((nb078AlphaDummy171), (nb078AlphaDummy172 f)),
                                      ((nb078AlphaDummy011), (nb078AlphaDummy014 f)),
                                      ((nb078AlphaDummy010), (nb078AlphaDummy013 f)),
                                      ((nb078AlphaDummy009), (nb078AlphaDummy012 f)),
                                      ((nb078AlphaDummy015), (nb078AlphaDummy016 f)),
                                      ((nb078AlphaDummy000), f),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
