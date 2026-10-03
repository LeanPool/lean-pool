/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part042`. -/


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
noncomputable def nb090_split_alpha_0018 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_177 A))
          (Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_177 A))
            (Class.cab (nb090_alpha_dummy_171 A)
              (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_178 h))
          (Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_178 h))
            (Class.cab (nb090_alpha_dummy_173 h)
              (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_172 A) from (by
                      unfold nb090_alpha_dummy_172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
                  (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_174 h) from (by
                      unfold nb090_alpha_dummy_174;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_171 A) from (by
                        unfold nb090_alpha_dummy_171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
                    (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_173 h) from (by
                        unfold nb090_alpha_dummy_173;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0166 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_177 A) from (by
                          unfold nb090_alpha_dummy_177;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0168 A) 0))))
                      (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_178 h) from (by
                          unfold nb090_alpha_dummy_178;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0169 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_175 A) from (by
                            unfold nb090_alpha_dummy_175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0165 A) 0))))
                        (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_176 h) from (by
                            unfold nb090_alpha_dummy_176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0167 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_129 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_179 A) from (by
                              unfold nb090_alpha_dummy_179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                          (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_181 h) from (by
                              unfold nb090_alpha_dummy_181;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_180 A) from (by
                                unfold nb090_alpha_dummy_180;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                            (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_182 h) from (by
                                unfold nb090_alpha_dummy_182;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_186 A) from (by
          unfold nb090_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 1)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_189 h) from (by
          unfold nb090_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_185 A) from (by
          unfold nb090_alpha_dummy_185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 0)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_188 h) from (by
          unfold nb090_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
          unfold nb090_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A)
                  0)))) (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
          unfold nb090_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A),
        (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A),
        (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A),
        (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A),
        (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A),
        (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A),
        (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_186
        A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187
        A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187
        A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                      (by
                                        unfold nb090_alpha_dummy_183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090_alpha_dummy_181 h) ≠
                                        (nb090_alpha_dummy_184 h) from (by
                                        unfold nb090_alpha_dummy_184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                                    ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                                    ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                                    ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                                    ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                                    ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
                                    ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                    (by
                                      unfold nb090_alpha_dummy_183;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0172 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from
                                    (by
                                      unfold nb090_alpha_dummy_184;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0173 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                      (by
                                        unfold nb090_alpha_dummy_183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090_alpha_dummy_181 h) ≠
                                        (nb090_alpha_dummy_184 h) from (by
                                        unfold nb090_alpha_dummy_184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                                    ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                                    ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                                    ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                                    ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                                    ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
                                    ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_172 A) from (by
                        unfold nb090_alpha_dummy_172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
                    (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_174 h) from (by
                        unfold nb090_alpha_dummy_174;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0166 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_171 A) from (by
                          unfold nb090_alpha_dummy_171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
                      (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_173 h) from (by
                          unfold nb090_alpha_dummy_173;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0166 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_177 A) from (by
                            unfold nb090_alpha_dummy_177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0168 A) 0))))
                        (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_178 h) from (by
                            unfold nb090_alpha_dummy_178;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0169 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_130 A) ≠ (nb090_alpha_dummy_175 A) from (by
                              unfold nb090_alpha_dummy_175;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0165 A) 0))))
                          (show (nb090_alpha_dummy_132 h) ≠ (nb090_alpha_dummy_176 h) from (by
                              unfold nb090_alpha_dummy_176;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0167 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_129 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_179 A) from (by
                                unfold nb090_alpha_dummy_179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                            (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_181 h) from (by
                                unfold nb090_alpha_dummy_181;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_180 A) from
                                (by
                                  unfold nb090_alpha_dummy_180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                              (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_182 h) from
                                (by
                                  unfold nb090_alpha_dummy_182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_172 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_174 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_186 A) from (by
          unfold nb090_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 1)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_189 h) from (by
          unfold nb090_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_185 A) from (by
          unfold nb090_alpha_dummy_185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A)
                  0)))) (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_188 h) from (by
          unfold nb090_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠
        (nb090_alpha_dummy_183 A) from (by
          unfold nb090_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A)
                  0)))) (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
          unfold nb090_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A),
        (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A),
        (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A),
        (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A),
        (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A),
        (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A),
        (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_186
        A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187
        A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187
        A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A)
                                        from (by
                                          unfold nb090_alpha_dummy_183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0172 A) 0)))) (show
                                        (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h)
                                        from (by
                                          unfold nb090_alpha_dummy_184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0173 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                                      ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                                      ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                                      ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                                      ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                                      ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
                                      ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                      (by
                                        unfold nb090_alpha_dummy_183;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0172 A)
                                                0)))) (show (nb090_alpha_dummy_181 h) ≠
                                        (nb090_alpha_dummy_184 h) from (by
                                        unfold nb090_alpha_dummy_184;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0173 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A)
                                        from (by
                                          unfold nb090_alpha_dummy_183;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0172 A) 0)))) (show
                                        (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h)
                                        from (by
                                          unfold nb090_alpha_dummy_184;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0173 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                                      ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                                      ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                                      ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                                      ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                                      ((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
                                      ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part043`. -/


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
noncomputable def nb090_split_alpha_0019 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
        ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_205 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_205 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_206 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_206 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_179 A) from (by
                      unfold nb090_alpha_dummy_179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                  (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_181 h) from (by
                      unfold nb090_alpha_dummy_181;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0171 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_180 A) from (by
                        unfold nb090_alpha_dummy_180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                    (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_182 h) from (by
                        unfold nb090_alpha_dummy_182;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_205 A) from (by
                          unfold nb090_alpha_dummy_205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                      (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_206 h) from (by
                          unfold nb090_alpha_dummy_206;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_203 A) from (by
                            unfold nb090_alpha_dummy_203;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                        (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_204 h) from (by
                            unfold nb090_alpha_dummy_204;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_186 A) from
                                      (by
                                        unfold nb090_alpha_dummy_186;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0174 A)
                                                1)))) (show (nb090_alpha_dummy_181 h) ≠
                                        (nb090_alpha_dummy_189 h) from (by
                                        unfold nb090_alpha_dummy_189;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0175 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_185 A)
                                        from (by
                                          unfold nb090_alpha_dummy_185;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 0)))) (show
                                        (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_188 h)
                                        from (by
                                          unfold nb090_alpha_dummy_188;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠
        (nb090_alpha_dummy_183 A) from (by
          unfold nb090_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_184 h) from (by
          unfold nb090_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_187 A),
        (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)),
                                        ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
                                        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                                        ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                                        ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                                        ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                                        ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                                        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                                        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                                        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                                        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                                        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)),
        ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A),
        (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
        ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A),
        (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
        ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A),
        (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
        ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A),
        (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                                unfold nb090_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                                unfold nb090_alpha_dummy_184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                            ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                            ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                            ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                            ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                            ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                            ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                            ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                            ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                            ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                            ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                            ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                              unfold nb090_alpha_dummy_183;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                          (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                              unfold nb090_alpha_dummy_184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                                unfold nb090_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                                unfold nb090_alpha_dummy_184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                            ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                            ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                            ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                            ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                            ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                            ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                            ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                            ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                            ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                            ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                            ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_179 A) from (by
                        unfold nb090_alpha_dummy_179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0170 A) 0))))
                    (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_181 h) from (by
                        unfold nb090_alpha_dummy_181;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0171 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_180 A) from (by
                          unfold nb090_alpha_dummy_180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0170 A) 1))))
                      (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_182 h) from (by
                          unfold nb090_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0171 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_205 A) from (by
                            unfold nb090_alpha_dummy_205;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0200 A) 0))))
                        (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_206 h) from (by
                            unfold nb090_alpha_dummy_206;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0201 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_172 A) ≠ (nb090_alpha_dummy_203 A) from (by
                              unfold nb090_alpha_dummy_203;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0198 A) 0))))
                          (show (nb090_alpha_dummy_174 h) ≠ (nb090_alpha_dummy_204 h) from (by
                              unfold nb090_alpha_dummy_204;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0199 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠
        (nb090_alpha_dummy_186 A) from (by
                                          unfold nb090_alpha_dummy_186;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0174 A) 1)))) (show
                                        (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_189 h)
                                        from (by
                                          unfold nb090_alpha_dummy_189;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0175 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_179 A) ≠
        (nb090_alpha_dummy_185 A) from (by
          unfold nb090_alpha_dummy_185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0174 A) 0)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_188 h) from (by
          unfold nb090_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0175 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
          unfold nb090_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0172 A) 0)))) (show (nb090_alpha_dummy_181 h) ≠
        (nb090_alpha_dummy_184 h) from (by
          unfold nb090_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0173 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_187 A),
        (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A), (nb090_alpha_dummy_189 h)),
        ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)), ((nb090_alpha_dummy_183 A),
        (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
        ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)), ((nb090_alpha_dummy_205 A),
        (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
        ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A),
        (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0178
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0179
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0176
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0177
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_193 A) from (by
          unfold
            nb090_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0182
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_194 h) from (by
          unfold
            nb090_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0183
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_191 A) from (by
          unfold
            nb090_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0180
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_192 h) from (by
          unfold
            nb090_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0181
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_187 A), (nb090_alpha_dummy_190 h)), ((nb090_alpha_dummy_186 A),
        (nb090_alpha_dummy_189 h)), ((nb090_alpha_dummy_185 A), (nb090_alpha_dummy_188 h)),
        ((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)), ((nb090_alpha_dummy_179 A),
        (nb090_alpha_dummy_181 h)), ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
        ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)), ((nb090_alpha_dummy_203 A),
        (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
        ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A),
        (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_197 A) from (by
          unfold
            nb090_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0186
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_198 h) from (by
          unfold
            nb090_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0187
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_186 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0184
                    A)
                  0)))) (show (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0185
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_179
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_187 A) ≠ (nb090_alpha_dummy_199 A) from (by
          unfold
            nb090_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0190
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_200 h) from (by
          unfold
            nb090_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0191
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_187 A) ≠
        (nb090_alpha_dummy_195 A) from (by
          unfold
            nb090_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0188
                    A)
                  0)))) (show (nb090_alpha_dummy_190 h) ≠ (nb090_alpha_dummy_196 h) from (by
          unfold
            nb090_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0189
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                (by
                                  unfold nb090_alpha_dummy_183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from
                                (by
                                  unfold nb090_alpha_dummy_184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                              ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                              ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                              ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                              ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                              ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                              ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                              ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                              ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                              ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                              ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                              ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from (by
                                unfold nb090_alpha_dummy_183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                            (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from (by
                                unfold nb090_alpha_dummy_184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_183 A) from
                                (by
                                  unfold nb090_alpha_dummy_183;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0172 A) 0))))
                              (show (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_184 h) from
                                (by
                                  unfold nb090_alpha_dummy_184;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0173 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_183 A), (nb090_alpha_dummy_184 h)),
                              ((nb090_alpha_dummy_179 A), (nb090_alpha_dummy_181 h)),
                              ((nb090_alpha_dummy_180 A), (nb090_alpha_dummy_182 h)),
                              ((nb090_alpha_dummy_205 A), (nb090_alpha_dummy_206 h)),
                              ((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)),
                              ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)),
                              ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)),
                              ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)),
                              ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                              ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                              ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                              ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part044`. -/


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
noncomputable def nb090_split_alpha_0020 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_213 A))
          (Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_213 A))
            (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_214 h))
          (Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_214 h))
            (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_208 A) from (by
                      unfold nb090_alpha_dummy_208;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
                  (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_210 h) from (by
                      unfold nb090_alpha_dummy_210;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_207 A) from (by
                        unfold nb090_alpha_dummy_207;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
                    (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_209 h) from (by
                        unfold nb090_alpha_dummy_209;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0216 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_213 A) from (by
                          unfold nb090_alpha_dummy_213;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0218 A) 0))))
                      (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_214 h) from (by
                          unfold nb090_alpha_dummy_214;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0219 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_211 A) from (by
                            unfold nb090_alpha_dummy_211;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0215 A) 0))))
                        (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_212 h) from (by
                            unfold nb090_alpha_dummy_212;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0217 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_050 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_215 A) from (by
                              unfold nb090_alpha_dummy_215;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0220 A) 0))))
                          (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_217 h) from (by
                              unfold nb090_alpha_dummy_217;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_216 A) from (by
                                unfold nb090_alpha_dummy_216;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0220 A) 1))))
                            (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_218 h) from (by
                                unfold nb090_alpha_dummy_218;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_208 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_210 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_222 A) from (by
          unfold nb090_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 1)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_225 h) from (by
          unfold nb090_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_221 A) from (by
          unfold nb090_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 0)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_224 h) from (by
          unfold nb090_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from (by
          unfold nb090_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0222 A)
                  0)))) (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
          unfold nb090_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A),
        (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A),
        (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_222
        A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                      (by
                                        unfold nb090_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_220 h) from (by
                                        unfold nb090_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                    ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                    ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                    ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                    ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                    ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
                                    ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                    (by
                                      unfold nb090_alpha_dummy_219;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0222 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from
                                    (by
                                      unfold nb090_alpha_dummy_220;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0223 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                      (by
                                        unfold nb090_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_220 h) from (by
                                        unfold nb090_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                    ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                    ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                    ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                    ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                    ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
                                    ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_208 A) from (by
                        unfold nb090_alpha_dummy_208;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
                    (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_210 h) from (by
                        unfold nb090_alpha_dummy_210;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0216 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_207 A) from (by
                          unfold nb090_alpha_dummy_207;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
                      (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_209 h) from (by
                          unfold nb090_alpha_dummy_209;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0216 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_213 A) from (by
                            unfold nb090_alpha_dummy_213;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0218 A) 0))))
                        (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_214 h) from (by
                            unfold nb090_alpha_dummy_214;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0219 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_211 A) from (by
                              unfold nb090_alpha_dummy_211;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0215 A) 0))))
                          (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_212 h) from (by
                              unfold nb090_alpha_dummy_212;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0217 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_050 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_215 A) from (by
                                unfold nb090_alpha_dummy_215;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0220 A) 0))))
                            (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_217 h) from (by
                                unfold nb090_alpha_dummy_217;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0221 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_208 A) ≠ (nb090_alpha_dummy_216 A) from
                                (by
                                  unfold nb090_alpha_dummy_216;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0220 A) 1))))
                              (show (nb090_alpha_dummy_210 h) ≠ (nb090_alpha_dummy_218 h) from
                                (by
                                  unfold nb090_alpha_dummy_218;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0221 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_208 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_210 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_222 A) from (by
          unfold nb090_alpha_dummy_222;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A) 1)))) (show (nb090_alpha_dummy_217 h) ≠
        (nb090_alpha_dummy_225 h) from (by
          unfold nb090_alpha_dummy_225;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_221 A) from (by
          unfold nb090_alpha_dummy_221;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0224 A)
                  0)))) (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_224 h) from (by
          unfold nb090_alpha_dummy_224;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0225 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_215 A) ≠
        (nb090_alpha_dummy_219 A) from (by
          unfold nb090_alpha_dummy_219;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0222 A)
                  0)))) (show (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h) from (by
          unfold nb090_alpha_dummy_220;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0223 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A),
        (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0228
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0229
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0226
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0227
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠ (nb090_alpha_dummy_229 A) from (by
          unfold
            nb090_alpha_dummy_229;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0232
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_230 h) from (by
          unfold
            nb090_alpha_dummy_230;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0233
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_227 A) from (by
          unfold
            nb090_alpha_dummy_227;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0230
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_228 h) from (by
          unfold
            nb090_alpha_dummy_228;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0231
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_223 A), (nb090_alpha_dummy_226 h)), ((nb090_alpha_dummy_222 A),
        (nb090_alpha_dummy_225 h)), ((nb090_alpha_dummy_221 A), (nb090_alpha_dummy_224 h)),
        ((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)), ((nb090_alpha_dummy_215 A),
        (nb090_alpha_dummy_217 h)), ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
        ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)), ((nb090_alpha_dummy_207 A),
        (nb090_alpha_dummy_209 h)), ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
        ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_217
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_222
        A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_233 A) from (by
          unfold
            nb090_alpha_dummy_233;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0236
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_234 h) from (by
          unfold
            nb090_alpha_dummy_234;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0237
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_222 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0234
                    A)
                  0)))) (show (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0235
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_215
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_223
        A) ≠ (nb090_alpha_dummy_235 A) from (by
          unfold
            nb090_alpha_dummy_235;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0240
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_236 h) from (by
          unfold
            nb090_alpha_dummy_236;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0241
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_223 A) ≠
        (nb090_alpha_dummy_231 A) from (by
          unfold
            nb090_alpha_dummy_231;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0238
                    A)
                  0)))) (show (nb090_alpha_dummy_226 h) ≠ (nb090_alpha_dummy_232 h) from (by
          unfold
            nb090_alpha_dummy_232;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0239
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A)
                                        from (by
                                          unfold nb090_alpha_dummy_219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0222 A) 0)))) (show
                                        (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h)
                                        from (by
                                          unfold nb090_alpha_dummy_220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0223 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                      ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                      ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                      ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                      ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                      ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
                                      ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A) from
                                      (by
                                        unfold nb090_alpha_dummy_219;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0222 A)
                                                0)))) (show (nb090_alpha_dummy_217 h) ≠
                                        (nb090_alpha_dummy_220 h) from (by
                                        unfold nb090_alpha_dummy_220;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0223 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_219 A)
                                        from (by
                                          unfold nb090_alpha_dummy_219;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0222 A) 0)))) (show
                                        (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_220 h)
                                        from (by
                                          unfold nb090_alpha_dummy_220;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0223 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_219 A), (nb090_alpha_dummy_220 h)),
                                      ((nb090_alpha_dummy_215 A), (nb090_alpha_dummy_217 h)),
                                      ((nb090_alpha_dummy_216 A), (nb090_alpha_dummy_218 h)),
                                      ((nb090_alpha_dummy_208 A), (nb090_alpha_dummy_210 h)),
                                      ((nb090_alpha_dummy_207 A), (nb090_alpha_dummy_209 h)),
                                      ((nb090_alpha_dummy_213 A), (nb090_alpha_dummy_214 h)),
                                      ((nb090_alpha_dummy_211 A), (nb090_alpha_dummy_212 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
