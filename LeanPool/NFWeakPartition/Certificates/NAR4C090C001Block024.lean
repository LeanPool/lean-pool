/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block023

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part069`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0047`. -/
@[expose]
noncomputable def nb090SplitAlpha0047 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
        ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy169 A))
          (synCphi (Class.cv (nb090AlphaDummy136 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy169 A))
            (synCphi (Class.cv (nb090AlphaDummy136 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy170 h))
          (synCphi (Class.cv (nb090AlphaDummy138 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy170 h))
            (synCphi (Class.cv (nb090AlphaDummy138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                      unfold nb090AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                  (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                      unfold nb090AlphaDummy145;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                        unfold nb090AlphaDummy144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                    (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                        unfold nb090AlphaDummy146;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy169 A) from (by
                          unfold nb090AlphaDummy169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                      (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy170 h) from (by
                          unfold nb090AlphaDummy170;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy167 A) from (by
                            unfold nb090AlphaDummy167;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                        (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy168 h) from (by
                            unfold nb090AlphaDummy168;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from
                                      (by
                                        unfold nb090AlphaDummy150;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0136 A)
                                                1)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy153 h) from (by
                                        unfold nb090AlphaDummy153;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0137 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A)
                                        from (by
                                          unfold nb090AlphaDummy149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy152 h)
                                        from (by
                                          unfold nb090AlphaDummy152;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy151 A),
        (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A), (nb090AlphaDummy153 h)),
                                        ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
                                        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                        ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                        ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                                        ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                                        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                                        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                        ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)),
        ((nb090AlphaDummy150 A), (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A),
        (nb090AlphaDummy152 h)), ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
        ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A),
        (nb090AlphaDummy146 h)), ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
        ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A),
        (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
        ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A),
        (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                unfold nb090AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                unfold nb090AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                            ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                            ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                            ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                            ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                            ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                            ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                            ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                            ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                            ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                            ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                              unfold nb090AlphaDummy147;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                          (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                              unfold nb090AlphaDummy148;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                unfold nb090AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                unfold nb090AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                            ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                            ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                            ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                            ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                            ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                            ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                            ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                            ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                            ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                            ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                        unfold nb090AlphaDummy143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                    (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                        unfold nb090AlphaDummy145;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                          unfold nb090AlphaDummy144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                      (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                          unfold nb090AlphaDummy146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy169 A) from (by
                            unfold nb090AlphaDummy169;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                        (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy170 h) from (by
                            unfold nb090AlphaDummy170;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy167 A) from (by
                              unfold nb090AlphaDummy167;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                          (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy168 h) from (by
                              unfold nb090AlphaDummy168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy150 A) from (by
                                          unfold nb090AlphaDummy150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 1)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy153 h)
                                        from (by
                                          unfold nb090AlphaDummy153;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy151 A),
        (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A), (nb090AlphaDummy153 h)),
        ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)), ((nb090AlphaDummy147 A),
        (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
        ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)), ((nb090AlphaDummy169 A),
        (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)), ((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A),
        (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                (by
                                  unfold nb090AlphaDummy147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                (by
                                  unfold nb090AlphaDummy148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                              ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                              ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                              ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                              ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                              ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                              ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                              ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                              ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                              ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                              ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
                                unfold nb090AlphaDummy147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
                                unfold nb090AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                (by
                                  unfold nb090AlphaDummy147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                (by
                                  unfold nb090AlphaDummy148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                              ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                              ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                              ((nb090AlphaDummy169 A), (nb090AlphaDummy170 h)),
                              ((nb090AlphaDummy167 A), (nb090AlphaDummy168 h)),
                              ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                              ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                              ((nb090AlphaDummy165 A), (nb090AlphaDummy166 h)),
                              ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                              ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                              ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part070`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0048`. -/
@[expose]
noncomputable def nb090SplitAlpha0048 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy177 A))
          (Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy177 A))
            (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCphi (Class.cv (nb090AlphaDummy172 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy178 h))
          (Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy178 h))
            (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCphi (Class.cv (nb090AlphaDummy174 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy172 A) from (by
                      unfold nb090AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
                  (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy174 h) from (by
                      unfold nb090AlphaDummy174;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy171 A) from (by
                        unfold nb090AlphaDummy171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
                    (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy173 h) from (by
                        unfold nb090AlphaDummy173;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0166 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy177 A) from (by
                          unfold nb090AlphaDummy177;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0168 A) 0))))
                      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy178 h) from (by
                          unfold nb090AlphaDummy178;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0169 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy175 A) from (by
                            unfold nb090AlphaDummy175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0165 A) 0))))
                        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy176 h) from (by
                            unfold nb090AlphaDummy176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0167 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy130 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy129 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy132 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy179 A) from (by
                              unfold nb090AlphaDummy179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                          (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy181 h) from (by
                              unfold nb090AlphaDummy181;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy180 A) from (by
                                unfold nb090AlphaDummy180;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                            (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy182 h) from (by
                                unfold nb090AlphaDummy182;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy186 A) from (by
          unfold nb090AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 1)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy189 h) from (by
          unfold nb090AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy185 A) from (by
          unfold nb090AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy188 h) from (by
          unfold nb090AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
          unfold nb090AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A)
                  0)))) (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186
        A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                      (by
                                        unfold nb090AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy184 h) from (by
                                        unfold nb090AlphaDummy184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                    ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                    ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                    ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                    ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                    ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                    ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                    ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                    ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                    (by
                                      unfold nb090AlphaDummy183;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0172 A)
                                              0)))) (show
                                    (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                    (by
                                      unfold nb090AlphaDummy184;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0173 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                      (by
                                        unfold nb090AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy184 h) from (by
                                        unfold nb090AlphaDummy184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                    ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                    ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                    ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                    ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                    ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                    ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                    ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                    ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy172 A) from (by
                        unfold nb090AlphaDummy172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
                    (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy174 h) from (by
                        unfold nb090AlphaDummy174;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0166 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy171 A) from (by
                          unfold nb090AlphaDummy171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
                      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy173 h) from (by
                          unfold nb090AlphaDummy173;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0166 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy177 A) from (by
                            unfold nb090AlphaDummy177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0168 A) 0))))
                        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy178 h) from (by
                            unfold nb090AlphaDummy178;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0169 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy175 A) from (by
                              unfold nb090AlphaDummy175;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0165 A) 0))))
                          (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy176 h) from (by
                              unfold nb090AlphaDummy176;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0167 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy130 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy129 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy132 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy179 A) from (by
                                unfold nb090AlphaDummy179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                            (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy181 h) from (by
                                unfold nb090AlphaDummy181;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy180 A) from
                                (by
                                  unfold nb090AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                              (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy182 h) from
                                (by
                                  unfold nb090AlphaDummy182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy172 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy174 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy186 A) from (by
          unfold nb090AlphaDummy186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 1)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy189 h) from (by
          unfold nb090AlphaDummy189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy185 A) from (by
          unfold nb090AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A)
                  0)))) (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy188 h) from (by
          unfold nb090AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy183 A) from (by
          unfold nb090AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A)
                  0)))) (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186
        A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187
        A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A)
                                        from (by
                                          unfold nb090AlphaDummy183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0172 A) 0)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h)
                                        from (by
                                          unfold nb090AlphaDummy184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0173 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                      ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                      ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                      ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                      ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                      ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                      ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                      ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                      ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                      (by
                                        unfold nb090AlphaDummy183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy184 h) from (by
                                        unfold nb090AlphaDummy184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A)
                                        from (by
                                          unfold nb090AlphaDummy183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0172 A) 0)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h)
                                        from (by
                                          unfold nb090AlphaDummy184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0173 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                      ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                      ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                      ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                      ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                      ((nb090AlphaDummy177 A), (nb090AlphaDummy178 h)),
                                      ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                      ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                      ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part071`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0049`. -/
@[expose]
noncomputable def nb090SplitAlpha0049 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
        ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy205 A))
          (synCphi (Class.cv (nb090AlphaDummy172 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy205 A))
            (synCphi (Class.cv (nb090AlphaDummy172 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy206 h))
          (synCphi (Class.cv (nb090AlphaDummy174 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy206 h))
            (synCphi (Class.cv (nb090AlphaDummy174 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy179 A) from (by
                      unfold nb090AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                  (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy181 h) from (by
                      unfold nb090AlphaDummy181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy180 A) from (by
                        unfold nb090AlphaDummy180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                    (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy182 h) from (by
                        unfold nb090AlphaDummy182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy205 A) from (by
                          unfold nb090AlphaDummy205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                      (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy206 h) from (by
                          unfold nb090AlphaDummy206;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy203 A) from (by
                            unfold nb090AlphaDummy203;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                        (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy204 h) from (by
                            unfold nb090AlphaDummy204;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy186 A) from
                                      (by
                                        unfold nb090AlphaDummy186;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0174 A)
                                                1)))) (show (nb090AlphaDummy181 h) ≠
                                        (nb090AlphaDummy189 h) from (by
                                        unfold nb090AlphaDummy189;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0175 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy185 A)
                                        from (by
                                          unfold nb090AlphaDummy185;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 0)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy188 h)
                                        from (by
                                          unfold nb090AlphaDummy188;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy183 A) from (by
          unfold nb090AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy187 A),
        (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A), (nb090AlphaDummy189 h)),
                                        ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
                                        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                                        ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                                        ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                                        ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                                        ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                                        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                                        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                                        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                                        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                                        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                        ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)),
        ((nb090AlphaDummy186 A), (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A),
        (nb090AlphaDummy188 h)), ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
        ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A),
        (nb090AlphaDummy182 h)), ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
        ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A),
        (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
        ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A),
        (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A),
        (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                unfold nb090AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                                unfold nb090AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                            ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                            ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                            ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                            ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                            ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                            ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                            ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                            ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                            ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                            ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                              unfold nb090AlphaDummy183;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                          (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                              unfold nb090AlphaDummy184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                unfold nb090AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                                unfold nb090AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                            ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                            ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                            ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                            ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                            ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                            ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                            ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                            ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                            ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                            ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                            ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                            ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                            ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                            ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy179 A) from (by
                        unfold nb090AlphaDummy179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                    (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy181 h) from (by
                        unfold nb090AlphaDummy181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy180 A) from (by
                          unfold nb090AlphaDummy180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                      (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy182 h) from (by
                          unfold nb090AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy205 A) from (by
                            unfold nb090AlphaDummy205;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                        (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy206 h) from (by
                            unfold nb090AlphaDummy206;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy172 A) ≠ (nb090AlphaDummy203 A) from (by
                              unfold nb090AlphaDummy203;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                          (show (nb090AlphaDummy174 h) ≠ (nb090AlphaDummy204 h) from (by
                              unfold nb090AlphaDummy204;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy186 A) from (by
                                          unfold nb090AlphaDummy186;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 1)))) (show
                                        (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy189 h)
                                        from (by
                                          unfold nb090AlphaDummy189;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy179 A) ≠
        (nb090AlphaDummy185 A) from (by
          unfold nb090AlphaDummy185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy188 h) from (by
          unfold nb090AlphaDummy188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
          unfold nb090AlphaDummy183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090AlphaDummy181 h) ≠
        (nb090AlphaDummy184 h) from (by
          unfold nb090AlphaDummy184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy187 A),
        (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A), (nb090AlphaDummy189 h)),
        ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)), ((nb090AlphaDummy183 A),
        (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
        ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)), ((nb090AlphaDummy205 A),
        (nb090AlphaDummy206 h)), ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
        ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)), ((nb090AlphaDummy171 A),
        (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
        ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy193 A) from (by
          unfold
            nb090AlphaDummy193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy194 h) from (by
          unfold
            nb090AlphaDummy194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy191 A) from (by
          unfold
            nb090AlphaDummy191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy192 h) from (by
          unfold
            nb090AlphaDummy192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy187 A), (nb090AlphaDummy190 h)), ((nb090AlphaDummy186 A),
        (nb090AlphaDummy189 h)), ((nb090AlphaDummy185 A), (nb090AlphaDummy188 h)),
        ((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)), ((nb090AlphaDummy179 A),
        (nb090AlphaDummy181 h)), ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
        ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)), ((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A),
        (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy197 A) from (by
          unfold
            nb090AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy198 h) from (by
          unfold
            nb090AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy186 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy179
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy187 A) ≠ (nb090AlphaDummy199 A) from (by
          unfold
            nb090AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy200 h) from (by
          unfold
            nb090AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy187 A) ≠
        (nb090AlphaDummy195 A) from (by
          unfold
            nb090AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090AlphaDummy190 h) ≠ (nb090AlphaDummy196 h) from (by
          unfold
            nb090AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                (by
                                  unfold nb090AlphaDummy183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                (by
                                  unfold nb090AlphaDummy184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                              ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                              ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                              ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                              ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                              ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                              ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                              ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                              ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                              ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                              ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from (by
                                unfold nb090AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from (by
                                unfold nb090AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy183 A) from
                                (by
                                  unfold nb090AlphaDummy183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy184 h) from
                                (by
                                  unfold nb090AlphaDummy184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy183 A), (nb090AlphaDummy184 h)),
                              ((nb090AlphaDummy179 A), (nb090AlphaDummy181 h)),
                              ((nb090AlphaDummy180 A), (nb090AlphaDummy182 h)),
                              ((nb090AlphaDummy205 A), (nb090AlphaDummy206 h)),
                              ((nb090AlphaDummy203 A), (nb090AlphaDummy204 h)),
                              ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
                              ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)),
                              ((nb090AlphaDummy201 A), (nb090AlphaDummy202 h)),
                              ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
                              ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                              ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                              ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                              ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                              ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                              ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
