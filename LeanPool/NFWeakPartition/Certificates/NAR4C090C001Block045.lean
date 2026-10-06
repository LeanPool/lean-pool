/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block044

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part121`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0098`. -/
@[expose]
noncomputable def nb090SplitAlpha0098 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (synWf1o (Class.cv (nb090AlphaDummy000 A))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
          (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))) (Wff.neg
          (synWral (nb090AlphaDummy041 A)
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
            (synWral (nb090AlphaDummy042 A)
              (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A))) (synWb
                (synWbr (Class.cv (nb090AlphaDummy041 A))
                  (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
                  (Class.cv (nb090AlphaDummy042 A))) (synWbr
                  (synCfv (Class.cv (nb090AlphaDummy000 A))
                    (Class.cv (nb090AlphaDummy041 A)))
                  (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
                  (synCfv (Class.cv (nb090AlphaDummy000 A))
                    (Class.cv (nb090AlphaDummy042 A)))))))))
      (Wff.imp (synWf1o (Class.cv h) (synCfv (synC2nd) (Class.cv u))
          (synCfv (synC2nd) (Class.cv v))) (Wff.neg
          (synWral (nb090AlphaDummy043 v u h) (synCfv (synC2nd) (Class.cv u))
            (synWral (nb090AlphaDummy044 v u h) (synCfv (synC2nd) (Class.cv u)) (synWb
                (synWbr (Class.cv (nb090AlphaDummy043 v u h))
                  (synCfv (synC1st) (Class.cv u)) (Class.cv (nb090AlphaDummy044 v u h)))
                (synWbr (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
                  (synCfv (synC1st) (Class.cv v))
                  (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h))))))))) :=
  (TAlphaWff.imp
    (TAlphaWff.conj (TAlphaWff.neg (nb090SplitAlpha0077 v u A h dv_h_u dv_h_v dv_u_v))
      (TAlphaWff.conj (TAlphaWff.conj (nb090SplitAlpha0022 v u A h) (TAlphaWff.classEq
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.reflOfClosed
                      [((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)),
                        ((nb090AlphaDummy243 A), (nb090AlphaDummy245 h)),
                        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                        ((nb090AlphaDummy001 A), u),
                        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                      (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                    (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj (nb090SplitAlpha0023 v u A h)
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.neg
        (nb090SplitAlpha0024 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.neg
        (nb090SplitAlpha0024 v u A h)))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                          (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (Ne.symm (show (nb090AlphaDummy130 A) ≠
                                        (nb090AlphaDummy133 A) from (by
                                        unfold nb090AlphaDummy133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0124 A)
                                                0))))) (Ne.symm (show
                                      (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy134 h) from
                                      (by
                                        unfold nb090AlphaDummy134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0125 h)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy133 A)
                                        from (by
                                          unfold nb090AlphaDummy133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0122 A) 0))))) (Ne.symm
                                      (show (nb090AlphaDummy131 h) ≠
        (nb090AlphaDummy134 h) from (by
                                          unfold nb090AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0123 h) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0025 v u A h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold
            nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold
            nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold
            nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold
            nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold
            nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold
            nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold
            nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold
            nb090AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy129 A))).fv ∪
        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090SplitAlpha0026 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
          unfold
            nb090AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
          unfold
            nb090AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy135 A) from (by
          unfold
            nb090AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold
            nb090AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy165 A) from (by
          unfold
            nb090AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy166 h) from (by
          unfold
            nb090AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy130 A) ≠
        (nb090AlphaDummy139 A) from (by
          unfold
            nb090AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy140 h) from (by
          unfold
            nb090AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy129 A))).fv ∪
        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090SplitAlpha0026 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy167 A),
        (nb090AlphaDummy168 h)), ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
        ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)), ((nb090AlphaDummy165 A),
        (nb090AlphaDummy166 h)), ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0027 v u A h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold
            nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold
            nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold
            nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold
            nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold
            nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold
            nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold
            nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold
            nb090AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090SplitAlpha0028 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
          unfold
            nb090AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
          unfold
            nb090AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy171 A) from (by
          unfold
            nb090AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold
            nb090AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy201 A) from (by
          unfold
            nb090AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy202 h) from (by
          unfold
            nb090AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy129 A) ≠
        (nb090AlphaDummy175 A) from (by
          unfold
            nb090AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy176 h) from (by
          unfold
            nb090AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv
        (nb090AlphaDummy129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090SplitAlpha0028 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy203 A),
        (nb090AlphaDummy204 h)), ((nb090AlphaDummy172 A), (nb090AlphaDummy174 h)),
        ((nb090AlphaDummy171 A), (nb090AlphaDummy173 h)), ((nb090AlphaDummy201 A),
        (nb090AlphaDummy202 h)), ((nb090AlphaDummy175 A), (nb090AlphaDummy176 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A),
        (nb090AlphaDummy131 h)), ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy244 A), (nb090AlphaDummy246 h)), ((nb090AlphaDummy243 A),
        (nb090AlphaDummy245 h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy130 A) from
                                    (by
                                      unfold nb090AlphaDummy130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0212 A)
                                              1)))) (show h ≠ (nb090AlphaDummy132 h) from (by
                                      unfold nb090AlphaDummy132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0213 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy129 A) from
                                      (by
                                        unfold nb090AlphaDummy129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0212 A)
                                                0)))) (show h ≠ (nb090AlphaDummy131 h) from
                                      (by
                                        unfold nb090AlphaDummy131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0213 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy133 A)
                                        from (by
                                          unfold nb090AlphaDummy133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0210 A) 0))))
                                      (show h ≠ (nb090AlphaDummy134 h) from (by
                                          unfold nb090AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0211 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy244 A) from (by
          unfold nb090AlphaDummy244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0290 A) 1)))) (show h ≠ (nb090AlphaDummy246 h) from (by
          unfold nb090AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0291 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy243 A) from (by
          unfold nb090AlphaDummy243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0290 A) 0)))) (show h ≠ (nb090AlphaDummy245 h) from (by
          unfold nb090AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0291 h) 0)))) (TAlphaVar.here _ _ _))))))))))))))))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                      (freshVar_injective (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq
                              (Class.cab (nb090AlphaDummy283 A)
                                (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                                  (Class.cv (nb090AlphaDummy283 A))))
                              (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) (by decide))
                      (freshVar_injective (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq
                              (Class.cab (nb090AlphaDummy284 u)
                                (synWbr (Class.cv u) (synC2nd)
                                  (Class.cv (nb090AlphaDummy284 u))))
                              (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) (by decide))
                      (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0029 v u A h dv_h_u dv_u_v))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold
            nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold
            nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0030 v u A h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold
            nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold
            nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0030 v u A h)))))))))))))))) (TAlphaClass.reflOfReflOn
                              [((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                                ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                  (nb090AlphaDummy004 v u A h))]
                              (synC2nd) (nb090WppRefl0108 v u A h)))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy285 A) ≠ (nb090AlphaDummy327 A) from (by
                                    unfold nb090AlphaDummy327;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0336 A)
                                            0)))) (show
                                  (nb090AlphaDummy286 u) ≠ (nb090AlphaDummy328 u) from (by
                                    unfold nb090AlphaDummy328;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0337 u)
                                            0)))) (TAlphaVar.here _ _ _)))))))))))))
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfClosed
                    [((nb090AlphaDummy334 A), (nb090AlphaDummy336 h)),
                      ((nb090AlphaDummy333 A), (nb090AlphaDummy335 h)),
                      ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                      ((nb090AlphaDummy001 A), u),
                      ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                    (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj (nb090SplitAlpha0035 v u A h)
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb090SplitAlpha0036 v u A h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb090SplitAlpha0036 v u A h))))))))))))
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy334 A) from (by
                          unfold nb090AlphaDummy334;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0380 A) 1))))
                      (show h ≠ (nb090AlphaDummy336 h) from (by
                          unfold nb090AlphaDummy336;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0381 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy333 A) from (by
                            unfold nb090AlphaDummy333;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0380 A) 0))))
                        (show h ≠ (nb090AlphaDummy335 h) from (by
                            unfold nb090AlphaDummy335;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0381 h) 0))))
                        (TAlphaVar.here _ _ _)))))))) (TAlphaClass.cab (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                      (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq
                            (Class.cab (nb090AlphaDummy373 A)
                              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
                                (Class.cv (nb090AlphaDummy373 A))))
                            (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv) (by decide))
                    (freshVar_injective (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq
                            (Class.cab (nb090AlphaDummy374 v)
                              (synWbr (Class.cv v) (synC2nd)
                                (Class.cv (nb090AlphaDummy374 v))))
                            (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv) (by decide))
                    (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.neg
                                        (nb090SplitAlpha0078 v u A h dv_h_v)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠ (nb090AlphaDummy382 A) from (by
          unfold nb090AlphaDummy382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy384 v) from (by
          unfold nb090AlphaDummy384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠
        (nb090AlphaDummy381 A) from (by
          unfold nb090AlphaDummy381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy383 v) from (by
          unfold nb090AlphaDummy383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠
        (nb090AlphaDummy411 A) from (by
          unfold
            nb090AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy412 v) from (by
          unfold
            nb090AlphaDummy412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠
        (nb090AlphaDummy385 A) from (by
          unfold
            nb090AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy386 v) from (by
          unfold
            nb090AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0079 v u A h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠ (nb090AlphaDummy382 A) from (by
          unfold nb090AlphaDummy382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy384 v) from (by
          unfold nb090AlphaDummy384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠
        (nb090AlphaDummy381 A) from (by
          unfold nb090AlphaDummy381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy383 v) from (by
          unfold nb090AlphaDummy383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠
        (nb090AlphaDummy411 A) from (by
          unfold
            nb090AlphaDummy411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy412 v) from (by
          unfold
            nb090AlphaDummy412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy373 A) ≠
        (nb090AlphaDummy385 A) from (by
          unfold
            nb090AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy386 v) from (by
          unfold
            nb090AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0079 v u A h)))))))))))))))) (TAlphaClass.reflOfReflOn
                            [((nb090AlphaDummy373 A), (nb090AlphaDummy374 v)),
                              ((nb090AlphaDummy375 A), (nb090AlphaDummy376 v)),
                              ((nb090AlphaDummy378 A), (nb090AlphaDummy380 v)),
                              ((nb090AlphaDummy377 A), (nb090AlphaDummy379 v)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synC2nd) (nb090WppRefl0267 v u A h)))) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy375 A) ≠ (nb090AlphaDummy417 A) from
                                (by
                                  unfold nb090AlphaDummy417;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0430 A) 0))))
                              (show (nb090AlphaDummy376 v) ≠ (nb090AlphaDummy418 v) from
                                (by
                                  unfold nb090AlphaDummy418;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0431 v) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg (TAlphaWff.all
        (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                      (freshVar_injective (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq
                              (Class.cab (nb090AlphaDummy283 A)
                                (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                                  (Class.cv (nb090AlphaDummy283 A))))
                              (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) (by decide))
                      (freshVar_injective (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq
                              (Class.cab (nb090AlphaDummy284 u)
                                (synWbr (Class.cv u) (synC2nd)
                                  (Class.cv (nb090AlphaDummy284 u))))
                              (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) (by decide))
                      (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0080 v u A h dv_h_u dv_u_v))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold
            nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold
            nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090SplitAlpha0081 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy323 A),
        (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
        ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)), ((nb090AlphaDummy321 A),
        (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A),
        (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002
        A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold
            nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold
            nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090SplitAlpha0081 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb090AlphaDummy323 A),
        (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A), (nb090AlphaDummy294 u)),
        ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)), ((nb090AlphaDummy321 A),
        (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A), (nb090AlphaDummy296 u)),
        ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)), ((nb090AlphaDummy285 A),
        (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
        ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002
        A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                              [((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                                ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                  (nb090AlphaDummy004 v u A h))]
                              (synC2nd) (nb090WppRefl0275 v u A h)))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy285 A) ≠ (nb090AlphaDummy327 A) from (by
                                    unfold nb090AlphaDummy327;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0336 A)
                                            0)))) (show
                                  (nb090AlphaDummy286 u) ≠ (nb090AlphaDummy328 u) from (by
                                    unfold nb090AlphaDummy328;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0337 u)
                                            0)))) (TAlphaVar.here _ _ _))))))))))))
          (TAlphaWff.all (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                          (freshVar_injective (((Class.cab (nb090AlphaDummy285 A)
                                (Wff.classEq (Class.cab (nb090AlphaDummy283 A)
                                    (synWbr (Class.cv (nb090AlphaDummy001 A))
                                      (synC2nd) (Class.cv (nb090AlphaDummy283 A))))
                                  (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq
                                  (Class.cab (nb090AlphaDummy284 u)
                                    (synWbr (Class.cv u) (synC2nd)
                                      (Class.cv (nb090AlphaDummy284 u))))
                                  (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0082 v u A h dv_h_u dv_u_v)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold
            nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold
            nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold
            nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold
            nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0083 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy323 A), (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A),
        (nb090AlphaDummy294 u)), ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
        ((nb090AlphaDummy321 A), (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A),
        (nb090AlphaDummy296 u)), ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
        ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A),
        (nb090AlphaDummy290 u)), ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002
        A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
          unfold
            nb090AlphaDummy292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
          unfold
            nb090AlphaDummy294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy291 A) from (by
          unfold
            nb090AlphaDummy291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold
            nb090AlphaDummy293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy321 A) from (by
          unfold
            nb090AlphaDummy321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy322 u) from (by
          unfold
            nb090AlphaDummy322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy283 A) ≠
        (nb090AlphaDummy295 A) from (by
          unfold
            nb090AlphaDummy295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy296 u) from (by
          unfold
            nb090AlphaDummy296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0083 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy323 A), (nb090AlphaDummy324 u)), ((nb090AlphaDummy292 A),
        (nb090AlphaDummy294 u)), ((nb090AlphaDummy291 A), (nb090AlphaDummy293 u)),
        ((nb090AlphaDummy321 A), (nb090AlphaDummy322 u)), ((nb090AlphaDummy295 A),
        (nb090AlphaDummy296 u)), ((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
        ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)), ((nb090AlphaDummy288 A),
        (nb090AlphaDummy290 u)), ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002
        A), v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb090AlphaDummy283 A), (nb090AlphaDummy284 u)),
                                    ((nb090AlphaDummy285 A), (nb090AlphaDummy286 u)),
                                    ((nb090AlphaDummy288 A), (nb090AlphaDummy290 u)),
                                    ((nb090AlphaDummy287 A), (nb090AlphaDummy289 u)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synC2nd) (nb090WppRefl0283 v u A h)))) (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy285 A) ≠ (nb090AlphaDummy327 A) from
                                      (by
                                        unfold nb090AlphaDummy327;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0336 A)
                                                0)))) (show (nb090AlphaDummy286 u) ≠
                                        (nb090AlphaDummy328 u) from (by
                                        unfold nb090AlphaDummy328;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0337 u)
                                                0)))) (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.conj (nb090SplitAlpha0096 v u A h dv_h_u dv_h_v dv_u_v)
                (nb090SplitAlpha0097 v u A h dv_h_u dv_h_v dv_u_v))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part122`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0099`. -/
@[expose]
noncomputable def nb090SplitAlpha0099 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v)
    (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classEq (Class.cv (nb090AlphaDummy003 A))
          (synCop (Class.cv (nb090AlphaDummy001 A)) (Class.cv (nb090AlphaDummy002 A))))
        (Wff.neg (synWa
            (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
              (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
            (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))))))
      (Wff.imp (Wff.classEq (Class.cv (nb090AlphaDummy004 v u A h))
          (synCop (Class.cv u) (Class.cv v))) (Wff.neg (synWa
            (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
              (Wff.classMem (Class.cv v) (synChwcodes A))) (synWex h
              (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
                (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
                (synCfv (synC2nd) (Class.cv v))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy003 A) from (by
                unfold nb090AlphaDummy003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0002 A) 0)))))
          (Ne.symm (show v ≠ (nb090AlphaDummy004 v u A h) from (by
                unfold nb090AlphaDummy004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0003 v u A h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy003 A) from (by
                  unfold nb090AlphaDummy003;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0000 A) 0)))))
            (Ne.symm (show u ≠ (nb090AlphaDummy004 v u A h) from (by
                  unfold nb090AlphaDummy004;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb090_support_mem_0001 v u A h) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy006 A) from
                                    (by
                                      unfold nb090AlphaDummy006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0004 A)
                                              1)))) (show u ≠ (nb090AlphaDummy008 v u) from
                                    (by
                                      unfold nb090AlphaDummy008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0006 v u)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy005 A) from
                                      (by
                                        unfold nb090AlphaDummy005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0004 A)
                                                0)))) (show u ≠ (nb090AlphaDummy007 v u) from
                                      (by
                                        unfold nb090AlphaDummy007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0006 v u) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy001 A) ≠
        (nb090AlphaDummy011 A) from (by
                                          unfold nb090AlphaDummy011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0008 A) 0))))
                                      (show u ≠ (nb090AlphaDummy012 v u) from (by
                                          unfold nb090AlphaDummy012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0009 v u) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy001 A) ≠
        (nb090AlphaDummy009 A) from (by
          unfold nb090AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0005 A) 0)))) (show u ≠ (nb090AlphaDummy010 v u) from
        (by
          unfold nb090AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0007 v u) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                                      ((Class.cv (nb090AlphaDummy002 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy013 A) from (by
          unfold nb090AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy015 v u) from (by
          unfold nb090AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy014 A) from (by
          unfold nb090AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy016 v u) from (by
          unfold nb090AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy006 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy008 v u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy020 A) from (by
          unfold
            nb090AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy023 v u) from (by
          unfold
            nb090AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy019 A) from (by
          unfold
            nb090AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy022 v u) from (by
          unfold
            nb090AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold
            nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold
            nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v
        u A h))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020
        A) ≠ (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy006 A) from
                                    (by
                                      unfold nb090AlphaDummy006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0004 A)
                                              1)))) (show u ≠ (nb090AlphaDummy008 v u) from
                                    (by
                                      unfold nb090AlphaDummy008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0006 v u)
                                              1)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy005 A) from
                                      (by
                                        unfold nb090AlphaDummy005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0004 A)
                                                0)))) (show u ≠ (nb090AlphaDummy007 v u) from
                                      (by
                                        unfold nb090AlphaDummy007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0006 v u) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy001 A) ≠
        (nb090AlphaDummy011 A) from (by
                                          unfold nb090AlphaDummy011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0008 A) 0))))
                                      (show u ≠ (nb090AlphaDummy012 v u) from (by
                                          unfold nb090AlphaDummy012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0009 v u) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy001 A) ≠
        (nb090AlphaDummy009 A) from (by
          unfold nb090AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0005 A) 0)))) (show u ≠ (nb090AlphaDummy010 v u) from
        (by
          unfold nb090AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0007 v u) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                                      ((Class.cv (nb090AlphaDummy002 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090AlphaDummy006 A) ≠
        (nb090AlphaDummy013 A) from (by
          unfold nb090AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy015 v u) from (by
          unfold nb090AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy006 A) ≠ (nb090AlphaDummy014 A) from (by
          unfold nb090AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090AlphaDummy008 v u) ≠
        (nb090AlphaDummy016 v u) from (by
          unfold nb090AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy006 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy008 v u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy020 A) from (by
          unfold
            nb090AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy023 v u) from (by
          unfold
            nb090AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy019 A) from (by
          unfold
            nb090AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy022 v u) from (by
          unfold
            nb090AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold
            nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold
            nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v
        u A h))] (synC1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy027 A) from (by
          unfold
            nb090AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy028 v u) from (by
          unfold
            nb090AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy025 A) from (by
          unfold
            nb090AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy026 v u) from (by
          unfold
            nb090AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy021 A), (nb090AlphaDummy024 v u)), ((nb090AlphaDummy020 A),
        (nb090AlphaDummy023 v u)), ((nb090AlphaDummy019 A), (nb090AlphaDummy022 v u)),
        ((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)), ((nb090AlphaDummy002 A),
        v), ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synC0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy020
        A) ≠ (nb090AlphaDummy031 A) from (by
          unfold
            nb090AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy032 v u) from (by
          unfold
            nb090AlphaDummy032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy020 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy013
        A))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy021
        A) ≠ (nb090AlphaDummy033 A) from (by
          unfold
            nb090AlphaDummy033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy034 v u) from (by
          unfold
            nb090AlphaDummy034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy021 A) ≠
        (nb090AlphaDummy029 A) from (by
          unfold
            nb090AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090AlphaDummy024 v u) ≠ (nb090AlphaDummy030 v u) from (by
          unfold
            nb090AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy013 A) ≠
        (nb090AlphaDummy017 A) from (by
          unfold nb090AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy018 v u) from (by
          unfold nb090AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy017 A), (nb090AlphaDummy018 v u)), ((nb090AlphaDummy013 A),
        (nb090AlphaDummy015 v u)), ((nb090AlphaDummy014 A), (nb090AlphaDummy016 v u)),
        ((nb090AlphaDummy006 A), (nb090AlphaDummy008 v u)), ((nb090AlphaDummy005 A),
        (nb090AlphaDummy007 v u)), ((nb090AlphaDummy011 A), (nb090AlphaDummy012 v u)),
        ((nb090AlphaDummy009 A), (nb090AlphaDummy010 v u)),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0000 v u A h)))))))))
    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
              (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_u_v
                (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfReflOn
              [((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
                ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
              (synChwcodes A) (nb090WppRefl0007 v u A h dv_A_u dv_A_v)))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.reflOfReflOn
              [((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
                ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
              (synChwcodes A) (nb090WppRefl0007 v u A h dv_A_u dv_A_v)))) (TAlphaWff.ex
          (TAlphaWff.neg (nb090SplitAlpha0098 v u A h dv_h_u dv_h_v dv_u_v))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_hwiso`. -/
@[expose]
noncomputable def nominalDfHwiso (v : Var) (u : Var) (A : Class) (h : Var)
    (_dv_A_h : h ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_h_u : h ≠ u)
    (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.classEq (synChwiso A) (synCopab u v (synWa
            (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
            (synWex h
              (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
              (nb090SplitAlpha0099 v u A h dv_A_u dv_A_v dv_h_u dv_h_v dv_u_v)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
