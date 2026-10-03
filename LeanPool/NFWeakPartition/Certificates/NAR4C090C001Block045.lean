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

@[expose]
noncomputable def nb090_split_alpha_0098 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (syn_wf1o (Class.cv (nb090_alpha_dummy_000 A))
          (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
          (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))) (Wff.neg
          (syn_wral (nb090_alpha_dummy_041 A)
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
            (syn_wral (nb090_alpha_dummy_042 A)
              (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A))) (syn_wb
                (syn_wbr (Class.cv (nb090_alpha_dummy_041 A))
                  (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
                  (Class.cv (nb090_alpha_dummy_042 A))) (syn_wbr
                  (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                    (Class.cv (nb090_alpha_dummy_041 A)))
                  (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
                  (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                    (Class.cv (nb090_alpha_dummy_042 A)))))))))
      (Wff.imp (syn_wf1o (Class.cv h) (syn_cfv (syn_c2nd) (Class.cv u))
          (syn_cfv (syn_c2nd) (Class.cv v))) (Wff.neg
          (syn_wral (nb090_alpha_dummy_043 v u h) (syn_cfv (syn_c2nd) (Class.cv u))
            (syn_wral (nb090_alpha_dummy_044 v u h) (syn_cfv (syn_c2nd) (Class.cv u)) (syn_wb
                (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h))
                  (syn_cfv (syn_c1st) (Class.cv u)) (Class.cv (nb090_alpha_dummy_044 v u h)))
                (syn_wbr (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
                  (syn_cfv (syn_c1st) (Class.cv v))
                  (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h))))))))) :=
  (TAlphaWff.imp
    (TAlphaWff.conj (TAlphaWff.neg (nb090_split_alpha_0077 v u A h dv_h_u dv_h_v dv_u_v))
      (TAlphaWff.conj (TAlphaWff.conj (nb090_split_alpha_0022 v u A h) (TAlphaWff.classEq
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.refl_of_closed
                      [((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)),
                        ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)),
                        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                        ((nb090_alpha_dummy_001 A), u),
                        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                      (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                    (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj (nb090_split_alpha_0023 v u A h)
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.neg
        (nb090_split_alpha_0024 v u A h))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.neg
        (nb090_split_alpha_0024 v u A h)))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                          (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (Ne.symm (show (nb090_alpha_dummy_130 A) ≠
                                        (nb090_alpha_dummy_133 A) from (by
                                        unfold nb090_alpha_dummy_133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0124 A)
                                                0))))) (Ne.symm (show
                                      (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_134 h) from
                                      (by
                                        unfold nb090_alpha_dummy_134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0125 h)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_133 A)
                                        from (by
                                          unfold nb090_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0122 A) 0))))) (Ne.symm
                                      (show (nb090_alpha_dummy_131 h) ≠
        (nb090_alpha_dummy_134 h) from (by
                                          unfold nb090_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0123 h) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0025 v u A h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold
            nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold
            nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold
            nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold
            nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold
            nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold
            nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold
            nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold
            nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090_split_alpha_0026 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004
        v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_136 A) from (by
          unfold
            nb090_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  1)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_138 h) from (by
          unfold
            nb090_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_135 A) from (by
          unfold
            nb090_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0154
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_137 h) from (by
          unfold
            nb090_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0156
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_165 A) from (by
          unfold
            nb090_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0158
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_166 h) from (by
          unfold
            nb090_alpha_dummy_166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0159
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_130 A) ≠
        (nb090_alpha_dummy_139 A) from (by
          unfold
            nb090_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0155
                    A)
                  0)))) (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_140 h) from (by
          unfold
            nb090_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0157
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090_split_alpha_0026 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004
        v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0027 v u A h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold
            nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold
            nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold
            nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold
            nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold
            nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold
            nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold
            nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold
            nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090_split_alpha_0028 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_203 A),
        (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A),
        (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004
        v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_172 A) from (by
          unfold
            nb090_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  1)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_174 h) from (by
          unfold
            nb090_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_171 A) from (by
          unfold
            nb090_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0192
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_173 h) from (by
          unfold
            nb090_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0194
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_201 A) from (by
          unfold
            nb090_alpha_dummy_201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0196
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_202 h) from (by
          unfold
            nb090_alpha_dummy_202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0197
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_129 A) ≠
        (nb090_alpha_dummy_175 A) from (by
          unfold
            nb090_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0193
                    A)
                  0)))) (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_176 h) from (by
          unfold
            nb090_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0195
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000
        A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv
        (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090_split_alpha_0028 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_203 A),
        (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A),
        (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A),
        (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004
        v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_130 A) from
                                    (by
                                      unfold nb090_alpha_dummy_130;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0212 A)
                                              1)))) (show h ≠ (nb090_alpha_dummy_132 h) from (by
                                      unfold nb090_alpha_dummy_132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0213 h)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_129 A) from
                                      (by
                                        unfold nb090_alpha_dummy_129;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0212 A)
                                                0)))) (show h ≠ (nb090_alpha_dummy_131 h) from
                                      (by
                                        unfold nb090_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0213 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_133 A)
                                        from (by
                                          unfold nb090_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0210 A) 0))))
                                      (show h ≠ (nb090_alpha_dummy_134 h) from (by
                                          unfold nb090_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0211 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_000 A) ≠
        (nb090_alpha_dummy_244 A) from (by
          unfold nb090_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0290 A) 1)))) (show h ≠ (nb090_alpha_dummy_246 h) from (by
          unfold nb090_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0291 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_243 A) from (by
          unfold nb090_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0290 A) 0)))) (show h ≠ (nb090_alpha_dummy_245 h) from (by
          unfold nb090_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0291 h) 0)))) (TAlphaVar.here _ _ _))))))))))))))))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                      (freshVar_injective (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq
                              (Class.cab (nb090_alpha_dummy_283 A)
                                (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                                  (Class.cv (nb090_alpha_dummy_283 A))))
                              (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) (by decide))
                      (freshVar_injective (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq
                              (Class.cab (nb090_alpha_dummy_284 u)
                                (syn_wbr (Class.cv u) (syn_c2nd)
                                  (Class.cv (nb090_alpha_dummy_284 u))))
                              (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) (by decide))
                      (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0029 v u A h dv_h_u dv_u_v))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
          unfold nb090_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
          unfold nb090_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_291 A) from (by
          unfold
            nb090_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold
            nb090_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_321 A) from (by
          unfold
            nb090_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_322 u) from (by
          unfold
            nb090_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_295 A) from (by
          unfold
            nb090_alpha_dummy_295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_296 u) from (by
          unfold
            nb090_alpha_dummy_296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0030 v u A h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
          unfold nb090_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
          unfold nb090_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_291 A) from (by
          unfold
            nb090_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold
            nb090_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_321 A) from (by
          unfold
            nb090_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_322 u) from (by
          unfold
            nb090_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_295 A) from (by
          unfold
            nb090_alpha_dummy_295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_296 u) from (by
          unfold
            nb090_alpha_dummy_296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0030 v u A h)))))))))))))))) (TAlphaClass.refl_of_reflOn
                              [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                                ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                  (nb090_alpha_dummy_004 v u A h))]
                              (syn_c2nd) (nb090_wpp_refl_0108 v u A h)))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_285 A) ≠ (nb090_alpha_dummy_327 A) from (by
                                    unfold nb090_alpha_dummy_327;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0336 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_286 u) ≠ (nb090_alpha_dummy_328 u) from (by
                                    unfold nb090_alpha_dummy_328;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0337 u)
                                            0)))) (TAlphaVar.here _ _ _)))))))))))))
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_closed
                    [((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)),
                      ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)),
                      ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                      ((nb090_alpha_dummy_001 A), u),
                      ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                    (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj (nb090_split_alpha_0035 v u A h)
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb090_split_alpha_0036 v u A h)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb090_split_alpha_0036 v u A h))))))))))))
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_334 A) from (by
                          unfold nb090_alpha_dummy_334;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0380 A) 1))))
                      (show h ≠ (nb090_alpha_dummy_336 h) from (by
                          unfold nb090_alpha_dummy_336;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0381 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_333 A) from (by
                            unfold nb090_alpha_dummy_333;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0380 A) 0))))
                        (show h ≠ (nb090_alpha_dummy_335 h) from (by
                            unfold nb090_alpha_dummy_335;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0381 h) 0))))
                        (TAlphaVar.here _ _ _)))))))) (TAlphaClass.cab (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                      (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq
                            (Class.cab (nb090_alpha_dummy_373 A)
                              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
                                (Class.cv (nb090_alpha_dummy_373 A))))
                            (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) (by decide))
                    (freshVar_injective (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq
                            (Class.cab (nb090_alpha_dummy_374 v)
                              (syn_wbr (Class.cv v) (syn_c2nd)
                                (Class.cv (nb090_alpha_dummy_374 v))))
                            (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) (by decide))
                    (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.neg
                                        (nb090_split_alpha_0078 v u A h dv_h_v)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠ (nb090_alpha_dummy_382 A) from (by
          unfold nb090_alpha_dummy_382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
          unfold nb090_alpha_dummy_384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_381 A) from (by
          unfold nb090_alpha_dummy_381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold nb090_alpha_dummy_383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_411 A) from (by
          unfold
            nb090_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_412 v) from (by
          unfold
            nb090_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_385 A) from (by
          unfold
            nb090_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_386 v) from (by
          unfold
            nb090_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0079 v u A h))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠ (nb090_alpha_dummy_382 A) from (by
          unfold nb090_alpha_dummy_382;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  1)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
          unfold nb090_alpha_dummy_384;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_381 A) from (by
          unfold nb090_alpha_dummy_381;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0420
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold nb090_alpha_dummy_383;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0422
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_411 A) from (by
          unfold
            nb090_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0424
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_412 v) from (by
          unfold
            nb090_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0425
                    v)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_373 A) ≠
        (nb090_alpha_dummy_385 A) from (by
          unfold
            nb090_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0421
                    A)
                  0)))) (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_386 v) from (by
          unfold
            nb090_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0423
                    v)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0079 v u A h)))))))))))))))) (TAlphaClass.refl_of_reflOn
                            [((nb090_alpha_dummy_373 A), (nb090_alpha_dummy_374 v)),
                              ((nb090_alpha_dummy_375 A), (nb090_alpha_dummy_376 v)),
                              ((nb090_alpha_dummy_378 A), (nb090_alpha_dummy_380 v)),
                              ((nb090_alpha_dummy_377 A), (nb090_alpha_dummy_379 v)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_c2nd) (nb090_wpp_refl_0267 v u A h)))) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_375 A) ≠ (nb090_alpha_dummy_417 A) from
                                (by
                                  unfold nb090_alpha_dummy_417;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0430 A) 0))))
                              (show (nb090_alpha_dummy_376 v) ≠ (nb090_alpha_dummy_418 v) from
                                (by
                                  unfold nb090_alpha_dummy_418;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0431 v) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg (TAlphaWff.all
        (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                      (freshVar_injective (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq
                              (Class.cab (nb090_alpha_dummy_283 A)
                                (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                                  (Class.cv (nb090_alpha_dummy_283 A))))
                              (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) (by decide))
                      (freshVar_injective (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq
                              (Class.cab (nb090_alpha_dummy_284 u)
                                (syn_wbr (Class.cv u) (syn_c2nd)
                                  (Class.cv (nb090_alpha_dummy_284 u))))
                              (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) (by decide))
                      (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb090_split_alpha_0080 v u A h dv_h_u dv_u_v))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
          unfold nb090_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
          unfold nb090_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_291 A) from (by
          unfold
            nb090_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold
            nb090_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_321 A) from (by
          unfold
            nb090_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_322 u) from (by
          unfold
            nb090_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_295 A) from (by
          unfold
            nb090_alpha_dummy_295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_296 u) from (by
          unfold
            nb090_alpha_dummy_296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090_split_alpha_0081 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_323 A),
        (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
        ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A),
        (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A),
        (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
          unfold nb090_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
          unfold nb090_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_291 A) from (by
          unfold
            nb090_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold
            nb090_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_321 A) from (by
          unfold
            nb090_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_322 u) from (by
          unfold
            nb090_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_295 A) from (by
          unfold
            nb090_alpha_dummy_295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_296 u) from (by
          unfold
            nb090_alpha_dummy_296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb090_split_alpha_0081 v u A h) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_323 A),
        (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)),
        ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A),
        (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)),
        ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A),
        (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
        ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                              [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                                ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                  (nb090_alpha_dummy_004 v u A h))]
                              (syn_c2nd) (nb090_wpp_refl_0275 v u A h)))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_285 A) ≠ (nb090_alpha_dummy_327 A) from (by
                                    unfold nb090_alpha_dummy_327;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0336 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_286 u) ≠ (nb090_alpha_dummy_328 u) from (by
                                    unfold nb090_alpha_dummy_328;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0337 u)
                                            0)))) (TAlphaVar.here _ _ _))))))))))))
          (TAlphaWff.all (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                          (freshVar_injective (((Class.cab (nb090_alpha_dummy_285 A)
                                (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A)
                                    (syn_wbr (Class.cv (nb090_alpha_dummy_001 A))
                                      (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A))))
                                  (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq
                                  (Class.cab (nb090_alpha_dummy_284 u)
                                    (syn_wbr (Class.cv u) (syn_c2nd)
                                      (Class.cv (nb090_alpha_dummy_284 u))))
                                  (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0082 v u A h dv_h_u dv_u_v)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
          unfold
            nb090_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
          unfold
            nb090_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_291 A) from (by
          unfold
            nb090_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold
            nb090_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_321 A) from (by
          unfold
            nb090_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_322 u) from (by
          unfold
            nb090_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_295 A) from (by
          unfold
            nb090_alpha_dummy_295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_296 u) from (by
          unfold
            nb090_alpha_dummy_296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0083 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A),
        (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
        ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A),
        (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
        ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A),
        (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
          unfold
            nb090_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  1)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
          unfold
            nb090_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_291 A) from (by
          unfold
            nb090_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0326
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold
            nb090_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0328
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_321 A) from (by
          unfold
            nb090_alpha_dummy_321;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0330
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_322 u) from (by
          unfold
            nb090_alpha_dummy_322;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0331
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_283 A) ≠
        (nb090_alpha_dummy_295 A) from (by
          unfold
            nb090_alpha_dummy_295;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0327
                    A)
                  0)))) (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_296 u) from (by
          unfold
            nb090_alpha_dummy_296;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0329
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0083 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A),
        (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)),
        ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A),
        (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
        ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A),
        (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002
        A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)),
                                    ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)),
                                    ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)),
                                    ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_c2nd) (nb090_wpp_refl_0283 v u A h)))) (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_285 A) ≠ (nb090_alpha_dummy_327 A) from
                                      (by
                                        unfold nb090_alpha_dummy_327;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0336 A)
                                                0)))) (show (nb090_alpha_dummy_286 u) ≠
                                        (nb090_alpha_dummy_328 u) from (by
                                        unfold nb090_alpha_dummy_328;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0337 u)
                                                0)))) (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.conj (nb090_split_alpha_0096 v u A h dv_h_u dv_h_v dv_u_v)
                (nb090_split_alpha_0097 v u A h dv_h_u dv_h_v dv_u_v))))))))

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

@[expose]
noncomputable def nb090_split_alpha_0099 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v)
    (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_003 A))
          (syn_cop (Class.cv (nb090_alpha_dummy_001 A)) (Class.cv (nb090_alpha_dummy_002 A))))
        (Wff.neg (syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
              (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
            (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
                (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))))
      (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_004 v u A h))
          (syn_cop (Class.cv u) (Class.cv v))) (Wff.neg (syn_wa
            (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
              (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h
              (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
                (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
                (syn_cfv (syn_c2nd) (Class.cv v))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_003 A) from (by
                unfold nb090_alpha_dummy_003;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0002 A) 0)))))
          (Ne.symm (show v ≠ (nb090_alpha_dummy_004 v u A h) from (by
                unfold nb090_alpha_dummy_004;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0003 v u A h) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_003 A) from (by
                  unfold nb090_alpha_dummy_003;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0000 A) 0)))))
            (Ne.symm (show u ≠ (nb090_alpha_dummy_004 v u A h) from (by
                  unfold nb090_alpha_dummy_004;
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
                                    (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_006 A) from
                                    (by
                                      unfold nb090_alpha_dummy_006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0004 A)
                                              1)))) (show u ≠ (nb090_alpha_dummy_008 v u) from
                                    (by
                                      unfold nb090_alpha_dummy_008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0006 v u)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_005 A) from
                                      (by
                                        unfold nb090_alpha_dummy_005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0004 A)
                                                0)))) (show u ≠ (nb090_alpha_dummy_007 v u) from
                                      (by
                                        unfold nb090_alpha_dummy_007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0006 v u) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_001 A) ≠
        (nb090_alpha_dummy_011 A) from (by
                                          unfold nb090_alpha_dummy_011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0008 A) 0))))
                                      (show u ≠ (nb090_alpha_dummy_012 v u) from (by
                                          unfold nb090_alpha_dummy_012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0009 v u) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_001 A) ≠
        (nb090_alpha_dummy_009 A) from (by
          unfold nb090_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0005 A) 0)))) (show u ≠ (nb090_alpha_dummy_010 v u) from
        (by
          unfold nb090_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0007 v u) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_002 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_013 A) from (by
          unfold nb090_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_015 v u) from (by
          unfold nb090_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_014 A) from (by
          unfold nb090_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_016 v u) from (by
          unfold nb090_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_006 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_008 v u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_020 A) from (by
          unfold
            nb090_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_023 v u) from (by
          unfold
            nb090_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_019 A) from (by
          unfold
            nb090_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_022 v u) from (by
          unfold
            nb090_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold
            nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold
            nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v
        u A h))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
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
        (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004
        v u A h))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020
        A) ≠ (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_006 A) from
                                    (by
                                      unfold nb090_alpha_dummy_006;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0004 A)
                                              1)))) (show u ≠ (nb090_alpha_dummy_008 v u) from
                                    (by
                                      unfold nb090_alpha_dummy_008;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0006 v u)
                                              1)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_005 A) from
                                      (by
                                        unfold nb090_alpha_dummy_005;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0004 A)
                                                0)))) (show u ≠ (nb090_alpha_dummy_007 v u) from
                                      (by
                                        unfold nb090_alpha_dummy_007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0006 v u) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_001 A) ≠
        (nb090_alpha_dummy_011 A) from (by
                                          unfold nb090_alpha_dummy_011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0008 A) 0))))
                                      (show u ≠ (nb090_alpha_dummy_012 v u) from (by
                                          unfold nb090_alpha_dummy_012;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0009 v u) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_001 A) ≠
        (nb090_alpha_dummy_009 A) from (by
          unfold nb090_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0005 A) 0)))) (show u ≠ (nb090_alpha_dummy_010 v u) from
        (by
          unfold nb090_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0007 v u) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                                      ((Class.cv (nb090_alpha_dummy_002 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv u)).fv ∪ ((Class.cv v)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_006 A) ≠
        (nb090_alpha_dummy_013 A) from (by
          unfold nb090_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 0)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_015 v u) from (by
          unfold nb090_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_006 A) ≠ (nb090_alpha_dummy_014 A) from (by
          unfold nb090_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0010 A) 1)))) (show (nb090_alpha_dummy_008 v u) ≠
        (nb090_alpha_dummy_016 v u) from (by
          unfold nb090_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0011 v u) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_006 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_008 v u))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_020 A) from (by
          unfold
            nb090_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  1)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_023 v u) from (by
          unfold
            nb090_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_019 A) from (by
          unfold
            nb090_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0014
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_022 v u) from (by
          unfold
            nb090_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0015
                    v u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold
            nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012
                    A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold
            nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013
                    v u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v
        u A h))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
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
        (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0018
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0019
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0016
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0017
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_027 A) from (by
          unfold
            nb090_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0022
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_028 v u) from (by
          unfold
            nb090_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0023
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_025 A) from (by
          unfold
            nb090_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0020
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_026 v u) from (by
          unfold
            nb090_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0021
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_021 A), (nb090_alpha_dummy_024 v u)), ((nb090_alpha_dummy_020 A),
        (nb090_alpha_dummy_023 v u)), ((nb090_alpha_dummy_019 A), (nb090_alpha_dummy_022 v u)),
        ((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)), ((nb090_alpha_dummy_002 A),
        v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004
        v u A h))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_020
        A) ≠ (nb090_alpha_dummy_031 A) from (by
          unfold
            nb090_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0026
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_032 v u) from (by
          unfold
            nb090_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0027
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_020 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0024
                    A)
                  0)))) (show (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0025
                    v
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_013
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_021
        A) ≠ (nb090_alpha_dummy_033 A) from (by
          unfold
            nb090_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0030
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_034 v u) from (by
          unfold
            nb090_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0031
                    v
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_021 A) ≠
        (nb090_alpha_dummy_029 A) from (by
          unfold
            nb090_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0028
                    A)
                  0)))) (show (nb090_alpha_dummy_024 v u) ≠ (nb090_alpha_dummy_030 v u) from (by
          unfold
            nb090_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0029
                    v
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v u)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_013 A) ≠
        (nb090_alpha_dummy_017 A) from (by
          unfold nb090_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0012 A)
                  0)))) (show (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_018 v u) from (by
          unfold nb090_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0013 v
                    u)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_017 A), (nb090_alpha_dummy_018 v u)), ((nb090_alpha_dummy_013 A),
        (nb090_alpha_dummy_015 v u)), ((nb090_alpha_dummy_014 A), (nb090_alpha_dummy_016 v u)),
        ((nb090_alpha_dummy_006 A), (nb090_alpha_dummy_008 v u)), ((nb090_alpha_dummy_005 A),
        (nb090_alpha_dummy_007 v u)), ((nb090_alpha_dummy_011 A), (nb090_alpha_dummy_012 v u)),
        ((nb090_alpha_dummy_009 A), (nb090_alpha_dummy_010 v u)),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0000 v u A h)))))))))
    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
              (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_u_v
                (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn
              [((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
                ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
              (syn_chwcodes A) (nb090_wpp_refl_0007 v u A h dv_A_u dv_A_v)))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.refl_of_reflOn
              [((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
                ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
              (syn_chwcodes A) (nb090_wpp_refl_0007 v u A h dv_A_u dv_A_v)))) (TAlphaWff.ex
          (TAlphaWff.neg (nb090_split_alpha_0098 v u A h dv_h_u dv_h_v dv_u_v))))))

@[expose]
noncomputable def nominal_df_hwiso (v : Var) (u : Var) (A : Class) (h : Var)
    (_dv_A_h : h ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_h_u : h ≠ u)
    (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.classEq (syn_chwiso A) (syn_copab u v (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
            (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
              (nb090_split_alpha_0099 v u A h dv_A_u dv_A_v dv_h_u dv_h_v dv_u_v)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
