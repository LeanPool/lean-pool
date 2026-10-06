/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C074C001Block003

/-! NF weak partition development: NAR4C074C001Part012. -/


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

/-- Checked nominal proof certificate identified upstream as `nb074_split_alpha_0008`. -/
@[expose]
noncomputable def nb074SplitAlpha0008 (x : Var) :
    TAlphaWff
      [((nb074AlphaDummy155), (nb074AlphaDummy156 x)),
        ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
        ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
        ((nb074AlphaDummy153), (nb074AlphaDummy154 x)),
        ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
        ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
        ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
        ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
        ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x),
        ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy155))
          (synCcompl (synCphi (Class.cv (nb074AlphaDummy124))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy155)) (synCcompl (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074AlphaDummy156 x))
          (synCcompl (synCphi (Class.cv (nb074AlphaDummy126 x))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074AlphaDummy156 x))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy157) from (by
                                  unfold nb074AlphaDummy157;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0160) 0))))
                              (show (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy158 x) from
                                (by
                                  unfold nb074AlphaDummy158;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0161 x) 0))))
                              (TAlphaVar.there
                                (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy155) from (by
                                    unfold nb074AlphaDummy155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0158) 0)))) (show
                                  (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy156 x) from (by
                                    unfold nb074AlphaDummy156;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0159 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb074AlphaDummy157), (nb074AlphaDummy158 x)), ((nb074AlphaDummy155),
        (nb074AlphaDummy156 x)), ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
        ((nb074AlphaDummy123), (nb074AlphaDummy125 x)), ((nb074AlphaDummy153),
        (nb074AlphaDummy154 x)), ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
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
        ((nb074AlphaDummy157), (nb074AlphaDummy158 x)), ((nb074AlphaDummy155),
        (nb074AlphaDummy156 x)), ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
        ((nb074AlphaDummy123), (nb074AlphaDummy125 x)), ((nb074AlphaDummy153),
        (nb074AlphaDummy154 x)), ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
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
                                    ((nb074AlphaDummy157), (nb074AlphaDummy158 x)),
                                    ((nb074AlphaDummy155), (nb074AlphaDummy156 x)),
                                    ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                    ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                    ((nb074AlphaDummy153), (nb074AlphaDummy154 x)),
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
                                    ((nb074AlphaDummy157), (nb074AlphaDummy158 x)),
                                    ((nb074AlphaDummy155), (nb074AlphaDummy156 x)),
                                    ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                    ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                    ((nb074AlphaDummy153), (nb074AlphaDummy154 x)),
                                    ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
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
                            (TAlphaVar.there
                              (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy157) from (by
                                  unfold nb074AlphaDummy157;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0160) 0))))
                              (show (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy158 x) from
                                (by
                                  unfold nb074AlphaDummy158;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0161 x) 0))))
                              (TAlphaVar.there
                                (show (nb074AlphaDummy124) ≠ (nb074AlphaDummy155) from (by
                                    unfold nb074AlphaDummy155;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0158) 0)))) (show
                                  (nb074AlphaDummy126 x) ≠ (nb074AlphaDummy156 x) from (by
                                    unfold nb074AlphaDummy156;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0159 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb074AlphaDummy157), (nb074AlphaDummy158 x)), ((nb074AlphaDummy155),
        (nb074AlphaDummy156 x)), ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
        ((nb074AlphaDummy123), (nb074AlphaDummy125 x)), ((nb074AlphaDummy153),
        (nb074AlphaDummy154 x)), ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
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
        ((nb074AlphaDummy157), (nb074AlphaDummy158 x)), ((nb074AlphaDummy155),
        (nb074AlphaDummy156 x)), ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
        ((nb074AlphaDummy123), (nb074AlphaDummy125 x)), ((nb074AlphaDummy153),
        (nb074AlphaDummy154 x)), ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
        ((nb074AlphaDummy082), (nb074AlphaDummy084 x)), ((nb074AlphaDummy081),
        (nb074AlphaDummy083 x)), ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
        ((nb074AlphaDummy042), (nb074AlphaDummy044 x)), ((nb074AlphaDummy041),
        (nb074AlphaDummy043 x)), ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
        ((nb074AlphaDummy000), x), ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
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
                                    ((nb074AlphaDummy157), (nb074AlphaDummy158 x)),
                                    ((nb074AlphaDummy155), (nb074AlphaDummy156 x)),
                                    ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                    ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                    ((nb074AlphaDummy153), (nb074AlphaDummy154 x)),
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
                                    ((nb074AlphaDummy157), (nb074AlphaDummy158 x)),
                                    ((nb074AlphaDummy155), (nb074AlphaDummy156 x)),
                                    ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
                                    ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
                                    ((nb074AlphaDummy153), (nb074AlphaDummy154 x)),
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
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.reflOfClosed [((nb074AlphaDummy155), (nb074AlphaDummy156 x)),
            ((nb074AlphaDummy124), (nb074AlphaDummy126 x)),
            ((nb074AlphaDummy123), (nb074AlphaDummy125 x)),
            ((nb074AlphaDummy153), (nb074AlphaDummy154 x)),
            ((nb074AlphaDummy127), (nb074AlphaDummy128 x)),
            ((nb074AlphaDummy082), (nb074AlphaDummy084 x)),
            ((nb074AlphaDummy081), (nb074AlphaDummy083 x)),
            ((nb074AlphaDummy085), (nb074AlphaDummy086 x)),
            ((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
            ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
            ((nb074AlphaDummy001), (nb074AlphaDummy002 x)), ((nb074AlphaDummy000), x),
            ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
          (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_domfn`. -/
@[expose]
noncomputable def nominalDfDomfn (x : Var) :
    Nominal.NPrf (.classEq (synCdomfn) (synCmpt x (synCvv) (synCdm (.cv x)))) := by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb074SplitAlpha0002 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy001) from (by
                          unfold nb074AlphaDummy001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0004) 0))))
                      (show x ≠ (nb074AlphaDummy002 x) from (by
                          unfold nb074AlphaDummy002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0005 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                      ((nb074AlphaDummy000), x),
                      ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                    (synCvv) (by simp only [fv_syn_cvv])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb074AlphaDummy042), (nb074AlphaDummy044 x)),
                              ((nb074AlphaDummy041), (nb074AlphaDummy043 x)),
                              ((nb074AlphaDummy001), (nb074AlphaDummy002 x)),
                              ((nb074AlphaDummy000), x),
                              ((nb074AlphaDummy003), (nb074AlphaDummy004 x))]
                            (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                          (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.neg (nb074SplitAlpha0004 x))))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
        (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy085) from (by
          unfold nb074AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0084) 0))))) (Ne.symm (show (nb074AlphaDummy084 x) ≠
        (nb074AlphaDummy086 x) from (by
          unfold nb074AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0085 x) 0))))) (TAlphaVar.there (Ne.symm (show
        (nb074AlphaDummy081) ≠ (nb074AlphaDummy085) from (by
          unfold nb074AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0082) 0))))) (Ne.symm (show (nb074AlphaDummy083 x) ≠
        (nb074AlphaDummy086 x) from (by
          unfold nb074AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0083 x) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074SplitAlpha0005 x))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy082) ≠
        (nb074AlphaDummy088) from (by
          unfold
            nb074AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  1)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy090 x) from (by
          unfold
            nb074AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy087)
        from (by
          unfold
            nb074AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  0)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy089 x) from (by
          unfold
            nb074AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy117)
        from (by
          unfold
            nb074AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0118)
                  0)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy118 x) from (by
          unfold
            nb074AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0119
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy091)
        from (by
          unfold
            nb074AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0115)
                  0)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy092 x) from (by
          unfold
            nb074AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0117
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy081))).fv ∪
        ((Class.cv (nb074AlphaDummy082))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074SplitAlpha0006 x))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy088) from (by
          unfold
            nb074AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  1)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy090 x) from (by
          unfold
            nb074AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy087)
        from (by
          unfold
            nb074AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0114)
                  0)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy089 x) from (by
          unfold
            nb074AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0116
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy117)
        from (by
          unfold
            nb074AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0118)
                  0)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy118 x) from (by
          unfold
            nb074AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0119
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy082) ≠ (nb074AlphaDummy091)
        from (by
          unfold
            nb074AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0115)
                  0)))) (show (nb074AlphaDummy084 x) ≠ (nb074AlphaDummy092 x) from (by
          unfold
            nb074AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0117
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy081))).fv ∪
        ((Class.cv (nb074AlphaDummy082))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy083 x))).fv ∪ ((Class.cv (nb074AlphaDummy084 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074SplitAlpha0006 x))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074SplitAlpha0007 x))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074AlphaDummy081) ≠
        (nb074AlphaDummy124) from (by
          unfold
            nb074AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  1)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy126 x) from (by
          unfold
            nb074AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy123)
        from (by
          unfold
            nb074AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  0)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy125 x) from (by
          unfold
            nb074AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy153)
        from (by
          unfold
            nb074AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0156)
                  0)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy154 x) from (by
          unfold
            nb074AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0157
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy127)
        from (by
          unfold
            nb074AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0153)
                  0)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy128 x) from (by
          unfold
            nb074AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy082))).fv ∪
        ((Class.cv (nb074AlphaDummy081))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074SplitAlpha0008 x))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy124) from (by
          unfold
            nb074AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  1)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy126 x) from (by
          unfold
            nb074AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  1)))) (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy123)
        from (by
          unfold
            nb074AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0152)
                  0)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy125 x) from (by
          unfold
            nb074AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0154
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy153)
        from (by
          unfold
            nb074AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0156)
                  0)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy154 x) from (by
          unfold
            nb074AlphaDummy154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0157
                    x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy081) ≠ (nb074AlphaDummy127)
        from (by
          unfold
            nb074AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0153)
                  0)))) (show (nb074AlphaDummy083 x) ≠ (nb074AlphaDummy128 x) from (by
          unfold
            nb074AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074AlphaDummy000))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074AlphaDummy082))).fv ∪
        ((Class.cv (nb074AlphaDummy081))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074AlphaDummy084 x))).fv ∪ ((Class.cv (nb074AlphaDummy083 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb074SplitAlpha0008 x)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074AlphaDummy000) ≠ (nb074AlphaDummy082) from (by
          unfold nb074AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0166) 1)))) (show x ≠ (nb074AlphaDummy084 x) from (by
          unfold nb074AlphaDummy084;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0167 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy000) ≠ (nb074AlphaDummy081) from (by
          unfold nb074AlphaDummy081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0166) 0)))) (show x ≠ (nb074AlphaDummy083 x) from (by
          unfold nb074AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0167 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy000) ≠ (nb074AlphaDummy085) from (by
          unfold nb074AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0164) 0)))) (show x ≠ (nb074AlphaDummy086 x) from (by
          unfold nb074AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0165 x) 0)))) (TAlphaVar.there (show
        (nb074AlphaDummy000) ≠ (nb074AlphaDummy042) from (by
          unfold nb074AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0162) 1)))) (show x ≠ (nb074AlphaDummy044 x) from (by
          unfold nb074AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0163 x) 1)))) (TAlphaVar.there (show
        (nb074AlphaDummy000) ≠ (nb074AlphaDummy041) from (by
          unfold nb074AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0162) 0)))) (show x ≠ (nb074AlphaDummy043 x) from (by
          unfold nb074AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0163 x)
                  0)))) (TAlphaVar.there (show (nb074AlphaDummy000) ≠ (nb074AlphaDummy001)
        from (by
          unfold nb074AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0004)
                  0)))) (show x ≠ (nb074AlphaDummy002 x) from (by
          unfold nb074AlphaDummy002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0005 x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
