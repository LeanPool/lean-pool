/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part011

/-! NF weak partition development: NAR4H5C095M3Part012. -/


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

@[expose]
noncomputable def nb095_split_alpha_0008 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_175 D R S_cls E), (nb095_alpha_dummy_176 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_175 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_175 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_169 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_170 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_169 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_176 f))
          (Class.cab (nb095_alpha_dummy_171 f)
            (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_176 f))
            (Class.cab (nb095_alpha_dummy_171 f)
              (syn_wrex (nb095_alpha_dummy_172 f) (Class.cv (nb095_alpha_dummy_016 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_171 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                      (nb095_alpha_dummy_170 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_172 f) from (by
                      unfold nb095_alpha_dummy_172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0174 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                        (nb095_alpha_dummy_169 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_171 f) from (by
                        unfold nb095_alpha_dummy_171;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0174 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                          (nb095_alpha_dummy_175 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_175;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0176 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_176 f) from (by
                          unfold nb095_alpha_dummy_176;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0177 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                            (nb095_alpha_dummy_173 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0173 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_174 f) from (by
                            unfold nb095_alpha_dummy_174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0175 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                              (nb095_alpha_dummy_177 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_177;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_179 f) from (by
                              unfold nb095_alpha_dummy_179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                (nb095_alpha_dummy_178 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_178;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_180 f) from (by
                                unfold nb095_alpha_dummy_180;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_172 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_184 D R S_cls E) from (by
          unfold nb095_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_187 f) from (by
          unfold nb095_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_183 D R S_cls E) from (by
          unfold nb095_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_186 f) from (by
          unfold nb095_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_181 D R S_cls E) from (by
          unfold nb095_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
          unfold nb095_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_175 D R S_cls E), (nb095_alpha_dummy_176 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_184
        D R S_cls E) ≠ (nb095_alpha_dummy_191 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_175 D R S_cls E), (nb095_alpha_dummy_176 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_177 D R S_cls E) ≠
                                        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                      (by
                                        unfold nb095_alpha_dummy_182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_181 D R S_cls E),
                                      (nb095_alpha_dummy_182 f)),
                                    ((nb095_alpha_dummy_177 D R S_cls E),
                                      (nb095_alpha_dummy_179 f)),
                                    ((nb095_alpha_dummy_178 D R S_cls E),
                                      (nb095_alpha_dummy_180 f)),
                                    ((nb095_alpha_dummy_170 D R S_cls E),
                                      (nb095_alpha_dummy_172 f)),
                                    ((nb095_alpha_dummy_169 D R S_cls E),
                                      (nb095_alpha_dummy_171 f)),
                                    ((nb095_alpha_dummy_175 D R S_cls E),
                                      (nb095_alpha_dummy_176 f)),
                                    ((nb095_alpha_dummy_173 D R S_cls E),
                                      (nb095_alpha_dummy_174 f)),
                                    ((nb095_alpha_dummy_013 D R S_cls E),
                                      (nb095_alpha_dummy_016 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
                                    ((nb095_alpha_dummy_009 D R S_cls E),
                                      (nb095_alpha_dummy_010 f)),
                                    ((nb095_alpha_dummy_007 D R S_cls E),
                                      (nb095_alpha_dummy_008 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_177 D R S_cls E) ≠
                                      (nb095_alpha_dummy_181 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                    (by
                                      unfold nb095_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_177 D R S_cls E) ≠
                                        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                      (by
                                        unfold nb095_alpha_dummy_182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_181 D R S_cls E),
                                      (nb095_alpha_dummy_182 f)),
                                    ((nb095_alpha_dummy_177 D R S_cls E),
                                      (nb095_alpha_dummy_179 f)),
                                    ((nb095_alpha_dummy_178 D R S_cls E),
                                      (nb095_alpha_dummy_180 f)),
                                    ((nb095_alpha_dummy_170 D R S_cls E),
                                      (nb095_alpha_dummy_172 f)),
                                    ((nb095_alpha_dummy_169 D R S_cls E),
                                      (nb095_alpha_dummy_171 f)),
                                    ((nb095_alpha_dummy_175 D R S_cls E),
                                      (nb095_alpha_dummy_176 f)),
                                    ((nb095_alpha_dummy_173 D R S_cls E),
                                      (nb095_alpha_dummy_174 f)),
                                    ((nb095_alpha_dummy_013 D R S_cls E),
                                      (nb095_alpha_dummy_016 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
                                    ((nb095_alpha_dummy_009 D R S_cls E),
                                      (nb095_alpha_dummy_010 f)),
                                    ((nb095_alpha_dummy_007 D R S_cls E),
                                      (nb095_alpha_dummy_008 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                        (nb095_alpha_dummy_170 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_172 f) from (by
                        unfold nb095_alpha_dummy_172;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0174 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                          (nb095_alpha_dummy_169 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0172 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_171 f) from (by
                          unfold nb095_alpha_dummy_171;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0174 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                            (nb095_alpha_dummy_175 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_175;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0176 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_176 f) from (by
                            unfold nb095_alpha_dummy_176;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0177 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_013 D R S_cls E) ≠
                              (nb095_alpha_dummy_173 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_173;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0173 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_174 f) from (by
                              unfold nb095_alpha_dummy_174;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0175 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_013 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_170 D R S_cls E) ≠
                                (nb095_alpha_dummy_177 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0178 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_179 f) from (by
                                unfold nb095_alpha_dummy_179;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                  (nb095_alpha_dummy_178 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0178 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_180 f) from
                                (by
                                  unfold nb095_alpha_dummy_180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_172 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_184 D R S_cls E) from (by
          unfold nb095_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_187 f) from (by
          unfold nb095_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_183 D R S_cls E) from (by
          unfold nb095_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_186 f) from (by
          unfold nb095_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
          unfold nb095_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
          unfold nb095_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_175 D R S_cls E), (nb095_alpha_dummy_176 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_184
        D R S_cls E) ≠ (nb095_alpha_dummy_191 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_175 D R S_cls E), (nb095_alpha_dummy_176 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185
        D R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_179 f) ≠
        (nb095_alpha_dummy_182 f) from (by
                                          unfold nb095_alpha_dummy_182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_181 D R S_cls E),
                                        (nb095_alpha_dummy_182 f)),
                                      ((nb095_alpha_dummy_177 D R S_cls E),
                                        (nb095_alpha_dummy_179 f)),
                                      ((nb095_alpha_dummy_178 D R S_cls E),
                                        (nb095_alpha_dummy_180 f)),
                                      ((nb095_alpha_dummy_170 D R S_cls E),
                                        (nb095_alpha_dummy_172 f)),
                                      ((nb095_alpha_dummy_169 D R S_cls E),
                                        (nb095_alpha_dummy_171 f)),
                                      ((nb095_alpha_dummy_175 D R S_cls E),
                                        (nb095_alpha_dummy_176 f)),
                                      ((nb095_alpha_dummy_173 D R S_cls E),
                                        (nb095_alpha_dummy_174 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_009 D R S_cls E),
                                        (nb095_alpha_dummy_010 f)),
                                      ((nb095_alpha_dummy_007 D R S_cls E),
                                        (nb095_alpha_dummy_008 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_177 D R S_cls E) ≠
                                        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_181;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                      (by
                                        unfold nb095_alpha_dummy_182;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_177 D R S_cls E) ≠
        (nb095_alpha_dummy_181 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_181;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0180 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_179 f) ≠
        (nb095_alpha_dummy_182 f) from (by
                                          unfold nb095_alpha_dummy_182;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_181 D R S_cls E),
                                        (nb095_alpha_dummy_182 f)),
                                      ((nb095_alpha_dummy_177 D R S_cls E),
                                        (nb095_alpha_dummy_179 f)),
                                      ((nb095_alpha_dummy_178 D R S_cls E),
                                        (nb095_alpha_dummy_180 f)),
                                      ((nb095_alpha_dummy_170 D R S_cls E),
                                        (nb095_alpha_dummy_172 f)),
                                      ((nb095_alpha_dummy_169 D R S_cls E),
                                        (nb095_alpha_dummy_171 f)),
                                      ((nb095_alpha_dummy_175 D R S_cls E),
                                        (nb095_alpha_dummy_176 f)),
                                      ((nb095_alpha_dummy_173 D R S_cls E),
                                        (nb095_alpha_dummy_174 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_009 D R S_cls E),
                                        (nb095_alpha_dummy_010 f)),
                                      ((nb095_alpha_dummy_007 D R S_cls E),
                                        (nb095_alpha_dummy_008 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0009 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095_alpha_dummy_201 D R S_cls E))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_170 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_202 f))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_172 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                            (nb095_alpha_dummy_177 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_179 f) from (by
                            unfold nb095_alpha_dummy_179;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                              (nb095_alpha_dummy_178 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_178;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_180 f) from (by
                              unfold nb095_alpha_dummy_180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                (nb095_alpha_dummy_203 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_203;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0208 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_204 f) from (by
                                unfold nb095_alpha_dummy_204;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0209 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                  (nb095_alpha_dummy_201 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_201;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0206 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_202 f) from
                                (by
                                  unfold nb095_alpha_dummy_202;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_172 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_184 D R S_cls E) from (by
          unfold nb095_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_187 f) from (by
          unfold nb095_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_183 D R S_cls E) from (by
          unfold nb095_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_186 f) from (by
          unfold nb095_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_181 D R S_cls E) from (by
          unfold nb095_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
          unfold nb095_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_184 D
        R S_cls E) ≠ (nb095_alpha_dummy_195 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185 D
        R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185 D
        R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_177 D R S_cls E) ≠
                                      (nb095_alpha_dummy_181 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                    (by
                                      unfold nb095_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_181 D R S_cls E),
                                    (nb095_alpha_dummy_182 f)),
                                  ((nb095_alpha_dummy_177 D R S_cls E),
                                    (nb095_alpha_dummy_179 f)),
                                  ((nb095_alpha_dummy_178 D R S_cls E),
                                    (nb095_alpha_dummy_180 f)),
                                  ((nb095_alpha_dummy_203 D R S_cls E),
                                    (nb095_alpha_dummy_204 f)),
                                  ((nb095_alpha_dummy_201 D R S_cls E),
                                    (nb095_alpha_dummy_202 f)),
                                  ((nb095_alpha_dummy_170 D R S_cls E),
                                    (nb095_alpha_dummy_172 f)),
                                  ((nb095_alpha_dummy_169 D R S_cls E),
                                    (nb095_alpha_dummy_171 f)),
                                  ((nb095_alpha_dummy_199 D R S_cls E),
                                    (nb095_alpha_dummy_200 f)),
                                  ((nb095_alpha_dummy_173 D R S_cls E),
                                    (nb095_alpha_dummy_174 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_177 D R S_cls E) ≠
                                    (nb095_alpha_dummy_181 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_181;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
                                    unfold nb095_alpha_dummy_182;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0181 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_177 D R S_cls E) ≠
                                      (nb095_alpha_dummy_181 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                    (by
                                      unfold nb095_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_181 D R S_cls E),
                                    (nb095_alpha_dummy_182 f)),
                                  ((nb095_alpha_dummy_177 D R S_cls E),
                                    (nb095_alpha_dummy_179 f)),
                                  ((nb095_alpha_dummy_178 D R S_cls E),
                                    (nb095_alpha_dummy_180 f)),
                                  ((nb095_alpha_dummy_203 D R S_cls E),
                                    (nb095_alpha_dummy_204 f)),
                                  ((nb095_alpha_dummy_201 D R S_cls E),
                                    (nb095_alpha_dummy_202 f)),
                                  ((nb095_alpha_dummy_170 D R S_cls E),
                                    (nb095_alpha_dummy_172 f)),
                                  ((nb095_alpha_dummy_169 D R S_cls E),
                                    (nb095_alpha_dummy_171 f)),
                                  ((nb095_alpha_dummy_199 D R S_cls E),
                                    (nb095_alpha_dummy_200 f)),
                                  ((nb095_alpha_dummy_173 D R S_cls E),
                                    (nb095_alpha_dummy_174 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                            (nb095_alpha_dummy_177 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_177;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_179 f) from (by
                            unfold nb095_alpha_dummy_179;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0179 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                              (nb095_alpha_dummy_178 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_178;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0178 D R S_cls E)
                                      1))))
                          (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_180 f) from (by
                              unfold nb095_alpha_dummy_180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0179 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                (nb095_alpha_dummy_203 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_203;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0208 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_204 f) from (by
                                unfold nb095_alpha_dummy_204;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0209 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_170 D R S_cls E) ≠
                                  (nb095_alpha_dummy_201 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_201;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0206 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_172 f) ≠ (nb095_alpha_dummy_202 f) from
                                (by
                                  unfold nb095_alpha_dummy_202;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0207 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_170 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095_alpha_dummy_172 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_184 D R S_cls E) from (by
          unfold nb095_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_187 f) from (by
          unfold nb095_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_183 D R S_cls E) from (by
          unfold nb095_alpha_dummy_183;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0182 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_186 f) from (by
          unfold nb095_alpha_dummy_186;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_177 D R S_cls E) ≠ (nb095_alpha_dummy_181 D R S_cls E) from (by
          unfold nb095_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0180 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
          unfold nb095_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0181 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0186
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0184
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠ (nb095_alpha_dummy_191
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0190
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_192 f) from (by
          unfold
            nb095_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_189 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0188
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_190 f) from (by
          unfold
            nb095_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_185 D R S_cls E), (nb095_alpha_dummy_188 f)),
        ((nb095_alpha_dummy_184 D R S_cls E), (nb095_alpha_dummy_187 f)),
        ((nb095_alpha_dummy_183 D R S_cls E), (nb095_alpha_dummy_186 f)),
        ((nb095_alpha_dummy_181 D R S_cls E), (nb095_alpha_dummy_182 f)),
        ((nb095_alpha_dummy_177 D R S_cls E), (nb095_alpha_dummy_179 f)),
        ((nb095_alpha_dummy_178 D R S_cls E), (nb095_alpha_dummy_180 f)),
        ((nb095_alpha_dummy_203 D R S_cls E), (nb095_alpha_dummy_204 f)),
        ((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_177 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_184 D
        R S_cls E) ≠ (nb095_alpha_dummy_195 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠ (nb095_alpha_dummy_195
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0194
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_196 f) from (by
          unfold
            nb095_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_184 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0192
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_187 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_177
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185 D
        R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_185 D
        R S_cls E) ≠ (nb095_alpha_dummy_197 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0198
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_198 f) from (by
          unfold
            nb095_alpha_dummy_198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_185 D R S_cls E) ≠
        (nb095_alpha_dummy_193 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0196
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_188 f) ≠ (nb095_alpha_dummy_194 f) from (by
          unfold
            nb095_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_177 D R S_cls E) ≠
                                      (nb095_alpha_dummy_181 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                    (by
                                      unfold nb095_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_181 D R S_cls E),
                                    (nb095_alpha_dummy_182 f)),
                                  ((nb095_alpha_dummy_177 D R S_cls E),
                                    (nb095_alpha_dummy_179 f)),
                                  ((nb095_alpha_dummy_178 D R S_cls E),
                                    (nb095_alpha_dummy_180 f)),
                                  ((nb095_alpha_dummy_203 D R S_cls E),
                                    (nb095_alpha_dummy_204 f)),
                                  ((nb095_alpha_dummy_201 D R S_cls E),
                                    (nb095_alpha_dummy_202 f)),
                                  ((nb095_alpha_dummy_170 D R S_cls E),
                                    (nb095_alpha_dummy_172 f)),
                                  ((nb095_alpha_dummy_169 D R S_cls E),
                                    (nb095_alpha_dummy_171 f)),
                                  ((nb095_alpha_dummy_199 D R S_cls E),
                                    (nb095_alpha_dummy_200 f)),
                                  ((nb095_alpha_dummy_173 D R S_cls E),
                                    (nb095_alpha_dummy_174 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_177 D R S_cls E) ≠
                                    (nb095_alpha_dummy_181 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_181;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from (by
                                    unfold nb095_alpha_dummy_182;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0181 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_177 D R S_cls E) ≠
                                      (nb095_alpha_dummy_181 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_181;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0180 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_179 f) ≠ (nb095_alpha_dummy_182 f) from
                                    (by
                                      unfold nb095_alpha_dummy_182;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_181 D R S_cls E),
                                    (nb095_alpha_dummy_182 f)),
                                  ((nb095_alpha_dummy_177 D R S_cls E),
                                    (nb095_alpha_dummy_179 f)),
                                  ((nb095_alpha_dummy_178 D R S_cls E),
                                    (nb095_alpha_dummy_180 f)),
                                  ((nb095_alpha_dummy_203 D R S_cls E),
                                    (nb095_alpha_dummy_204 f)),
                                  ((nb095_alpha_dummy_201 D R S_cls E),
                                    (nb095_alpha_dummy_202 f)),
                                  ((nb095_alpha_dummy_170 D R S_cls E),
                                    (nb095_alpha_dummy_172 f)),
                                  ((nb095_alpha_dummy_169 D R S_cls E),
                                    (nb095_alpha_dummy_171 f)),
                                  ((nb095_alpha_dummy_199 D R S_cls E),
                                    (nb095_alpha_dummy_200 f)),
                                  ((nb095_alpha_dummy_173 D R S_cls E),
                                    (nb095_alpha_dummy_174 f)),
                                  ((nb095_alpha_dummy_013 D R S_cls E),
                                    (nb095_alpha_dummy_016 f)),
                                  ((nb095_alpha_dummy_012 D R S_cls E),
                                    (nb095_alpha_dummy_015 f)),
                                  ((nb095_alpha_dummy_011 D R S_cls E),
                                    (nb095_alpha_dummy_014 f)),
                                  ((nb095_alpha_dummy_017 D R S_cls E),
                                    (nb095_alpha_dummy_018 f)),
                                  ((nb095_alpha_dummy_009 D R S_cls E),
                                    (nb095_alpha_dummy_010 f)),
                                  ((nb095_alpha_dummy_007 D R S_cls E),
                                    (nb095_alpha_dummy_008 f)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0010 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classEq (Class.cv (nb095_alpha_dummy_017 D R S_cls E))
          (syn_cop (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))) (Wff.neg
          (syn_wex (nb095_alpha_dummy_013 D R S_cls E) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (syn_ccnv (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
                (Class.cv (nb095_alpha_dummy_013 D R S_cls E)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_013 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_012 D R S_cls E)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb095_alpha_dummy_018 f))
          (syn_cop (Class.cv (nb095_alpha_dummy_014 f)) (Class.cv (nb095_alpha_dummy_015 f))))
        (Wff.neg (syn_wex (nb095_alpha_dummy_016 f) (syn_wa
              (syn_wbr (Class.cv (nb095_alpha_dummy_014 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb095_alpha_dummy_016 f)))
              (syn_wbr (Class.cv (nb095_alpha_dummy_016 f)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_015 f))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
              (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_017 D R S_cls E) from (by
                unfold nb095_alpha_dummy_017;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0002 D R S_cls E) 0))))) (Ne.symm
            (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_018 f) from (by
                unfold nb095_alpha_dummy_018;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0003 f) 0)))))
          (TAlphaVar.there (Ne.symm (show
                (nb095_alpha_dummy_011 D R S_cls E) ≠ (nb095_alpha_dummy_017 D R S_cls E) from
                (by
                  unfold nb095_alpha_dummy_017;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0000 D R S_cls E) 0))))) (Ne.symm
              (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_018 f) from (by
                  unfold nb095_alpha_dummy_018;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0001 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0000 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_012 D R S_cls E) ≠
                                      (nb095_alpha_dummy_020 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0032 D R S_cls E) 1)))) (show
                                    (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_022 f) from
                                    (by
                                      unfold nb095_alpha_dummy_022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_012 D R S_cls E) ≠
                                        (nb095_alpha_dummy_019 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0032 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_021 f) from
                                      (by
                                        unfold nb095_alpha_dummy_021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_049 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_049;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0036 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_015 f) ≠
        (nb095_alpha_dummy_050 f) from (by
                                          unfold nb095_alpha_dummy_050;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_023 D R S_cls E) from (by
          unfold nb095_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0033 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_024 f) from (by
          unfold nb095_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg
                                    (nb095_split_alpha_0001 x u D R S_cls f E)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_012 D R S_cls E) ≠
                                      (nb095_alpha_dummy_020 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_020;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0032 D R S_cls E) 1)))) (show
                                    (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_022 f) from
                                    (by
                                      unfold nb095_alpha_dummy_022;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0034 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_012 D R S_cls E) ≠
                                        (nb095_alpha_dummy_019 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0032 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_021 f) from
                                      (by
                                        unfold nb095_alpha_dummy_021;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0034 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_012 D R S_cls E) ≠
        (nb095_alpha_dummy_049 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_049;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0036 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_015 f) ≠
        (nb095_alpha_dummy_050 f) from (by
                                          unfold nb095_alpha_dummy_050;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0037 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_023 D R S_cls E) from (by
          unfold nb095_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0033 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_024 f) from (by
          unfold nb095_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0035 f) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
                                      ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb095_split_alpha_0001 x u D R S_cls f
                                      E))))))))))))))))) (TAlphaWff.neg (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg
                        (TAlphaWff.neg (nb095_split_alpha_0002 x u D R S_cls f E)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
          unfold nb095_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_058 f) from (by
          unfold nb095_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_085 D R S_cls E) from (by
          unfold nb095_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_086 f) from (by
          unfold nb095_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_059 D R S_cls E) from (by
          unfold nb095_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_060 f) from (by
          unfold nb095_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_011 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_013 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095_split_alpha_0003 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_087 D R S_cls E), (nb095_alpha_dummy_088 f)),
        ((nb095_alpha_dummy_056 D R S_cls E), (nb095_alpha_dummy_058 f)),
        ((nb095_alpha_dummy_055 D R S_cls E), (nb095_alpha_dummy_057 f)),
        ((nb095_alpha_dummy_085 D R S_cls E), (nb095_alpha_dummy_086 f)),
        ((nb095_alpha_dummy_059 D R S_cls E), (nb095_alpha_dummy_060 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_056 D R S_cls E) from (by
          unfold nb095_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_058 f) from (by
          unfold nb095_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_055 D R S_cls E) from (by
          unfold nb095_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_057 f) from (by
          unfold nb095_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_085 D R S_cls E) from (by
          unfold nb095_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_086 f) from (by
          unfold nb095_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_013 D R S_cls E) ≠ (nb095_alpha_dummy_059 D R S_cls E) from (by
          unfold nb095_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_016 f) ≠ (nb095_alpha_dummy_060 f) from (by
          unfold nb095_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073 f) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_011 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_013 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_016 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095_split_alpha_0003 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_087 D R S_cls E), (nb095_alpha_dummy_088 f)),
        ((nb095_alpha_dummy_056 D R S_cls E), (nb095_alpha_dummy_058 f)),
        ((nb095_alpha_dummy_055 D R S_cls E), (nb095_alpha_dummy_057 f)),
        ((nb095_alpha_dummy_085 D R S_cls E), (nb095_alpha_dummy_086 f)),
        ((nb095_alpha_dummy_059 D R S_cls E), (nb095_alpha_dummy_060 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                                (nb095_alpha_dummy_095 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_095;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0082 D R S_cls E) 0))))) (Ne.symm
                            (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_096 f) from (by
                                unfold nb095_alpha_dummy_096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0083 f) 0)))))
                          (TAlphaVar.there (Ne.symm (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                                  (nb095_alpha_dummy_095 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0080 D R S_cls E) 0))))) (Ne.symm
                              (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_096 f) from
                                (by
                                  unfold nb095_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0081 f) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095_split_alpha_0004 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0005 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_129 D R S_cls
        E), (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_013 D R S_cls E),
        (nb095_alpha_dummy_016 f)), ((nb095_alpha_dummy_012 D R S_cls E),
        (nb095_alpha_dummy_015 f)), ((nb095_alpha_dummy_011 D R S_cls E),
        (nb095_alpha_dummy_014 f)), ((nb095_alpha_dummy_017 D R S_cls E),
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_009 D R S_cls E),
        (nb095_alpha_dummy_010 f)), ((nb095_alpha_dummy_007 D R S_cls E),
        (nb095_alpha_dummy_008 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0005 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_129 D R S_cls
        E), (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_013 D R S_cls E),
        (nb095_alpha_dummy_016 f)), ((nb095_alpha_dummy_012 D R S_cls E),
        (nb095_alpha_dummy_015 f)), ((nb095_alpha_dummy_011 D R S_cls E),
        (nb095_alpha_dummy_014 f)), ((nb095_alpha_dummy_017 D R S_cls E),
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_009 D R S_cls E),
        (nb095_alpha_dummy_010 f)), ((nb095_alpha_dummy_007 D R S_cls E),
        (nb095_alpha_dummy_008 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095_split_alpha_0006 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0007 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_165 D R S_cls
        E), (nb095_alpha_dummy_166 f)), ((nb095_alpha_dummy_134 D R S_cls E),
        (nb095_alpha_dummy_136 f)), ((nb095_alpha_dummy_133 D R S_cls E),
        (nb095_alpha_dummy_135 f)), ((nb095_alpha_dummy_163 D R S_cls E),
        (nb095_alpha_dummy_164 f)), ((nb095_alpha_dummy_137 D R S_cls E),
        (nb095_alpha_dummy_138 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_013 D R S_cls E),
        (nb095_alpha_dummy_016 f)), ((nb095_alpha_dummy_012 D R S_cls E),
        (nb095_alpha_dummy_015 f)), ((nb095_alpha_dummy_011 D R S_cls E),
        (nb095_alpha_dummy_014 f)), ((nb095_alpha_dummy_017 D R S_cls E),
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_009 D R S_cls E),
        (nb095_alpha_dummy_010 f)), ((nb095_alpha_dummy_007 D R S_cls E),
        (nb095_alpha_dummy_008 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_091 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
        ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0007 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_165 D R S_cls
        E), (nb095_alpha_dummy_166 f)), ((nb095_alpha_dummy_134 D R S_cls E),
        (nb095_alpha_dummy_136 f)), ((nb095_alpha_dummy_133 D R S_cls E),
        (nb095_alpha_dummy_135 f)), ((nb095_alpha_dummy_163 D R S_cls E),
        (nb095_alpha_dummy_164 f)), ((nb095_alpha_dummy_137 D R S_cls E),
        (nb095_alpha_dummy_138 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_013 D R S_cls E),
        (nb095_alpha_dummy_016 f)), ((nb095_alpha_dummy_012 D R S_cls E),
        (nb095_alpha_dummy_015 f)), ((nb095_alpha_dummy_011 D R S_cls E),
        (nb095_alpha_dummy_014 f)), ((nb095_alpha_dummy_017 D R S_cls E),
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_009 D R S_cls E),
        (nb095_alpha_dummy_010 f)), ((nb095_alpha_dummy_007 D R S_cls E),
        (nb095_alpha_dummy_008 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                            (nb095_alpha_dummy_000 D R S_cls E) ≠
                              (nb095_alpha_dummy_092 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_092;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0170 D R S_cls E)
                                      1)))) (show f ≠ (nb095_alpha_dummy_094 f) from (by
                              unfold nb095_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0171 f) 1))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                (nb095_alpha_dummy_091 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0170 D R S_cls E) 0))))
                            (show f ≠ (nb095_alpha_dummy_093 f) from (by
                                unfold nb095_alpha_dummy_093;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0171 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                  (nb095_alpha_dummy_095 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0168 D R S_cls E) 0))))
                              (show f ≠ (nb095_alpha_dummy_096 f) from (by
                                  unfold nb095_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0169 f) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                                    (nb095_alpha_dummy_013 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0164 D R S_cls E) 2))))
                                (show f ≠ (nb095_alpha_dummy_016 f) from (by
                                    unfold nb095_alpha_dummy_016;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0166 f)
                                            2)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_000 D R S_cls E) ≠
                                      (nb095_alpha_dummy_012 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_012;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0164 D R S_cls E) 1))))
                                  (show f ≠ (nb095_alpha_dummy_015 f) from (by
                                      unfold nb095_alpha_dummy_015;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0166 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_011 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_011;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0164 D R S_cls E) 0))))
                                    (show f ≠ (nb095_alpha_dummy_014 f) from (by
                                        unfold nb095_alpha_dummy_014;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0166 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_017 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0165 D R S_cls E)
                                                  0)))) (show f ≠ (nb095_alpha_dummy_018 f) from
                                        (by
                                          unfold nb095_alpha_dummy_018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0167 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_009 D R S_cls E) from (by
          unfold nb095_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0162 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_010 f) from (by
          unfold nb095_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_007 D R S_cls E) from (by
          unfold nb095_alpha_dummy_007;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0160 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_008 f) from (by
          unfold nb095_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0161 f) 0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg
                        (TAlphaWff.neg (nb095_split_alpha_0008 x u D R S_cls f E)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
          unfold nb095_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_172 f) from (by
          unfold nb095_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_199 D R S_cls E) from (by
          unfold nb095_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_200 f) from (by
          unfold nb095_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_173 D R S_cls E) from (by
          unfold nb095_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_174 f) from (by
          unfold nb095_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_ccnv (Class.cv
        (nb095_alpha_dummy_000 D R S_cls E)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_013 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_012 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095_split_alpha_0009 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_170 D R S_cls E) from (by
          unfold nb095_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_172 f) from (by
          unfold nb095_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_169 D R S_cls E) from (by
          unfold nb095_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_171 f) from (by
          unfold nb095_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_199 D R S_cls E) from (by
          unfold nb095_alpha_dummy_199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_200 f) from (by
          unfold nb095_alpha_dummy_200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_012 D R S_cls E) ≠ (nb095_alpha_dummy_173 D R S_cls E) from (by
          unfold nb095_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_015 f) ≠ (nb095_alpha_dummy_174 f) from (by
          unfold nb095_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_ccnv (Class.cv
        (nb095_alpha_dummy_000 D R S_cls E)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_013 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_012 D R S_cls E))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_016 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_015 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (nb095_split_alpha_0009 x u D R S_cls f E) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_201 D R S_cls E), (nb095_alpha_dummy_202 f)),
        ((nb095_alpha_dummy_170 D R S_cls E), (nb095_alpha_dummy_172 f)),
        ((nb095_alpha_dummy_169 D R S_cls E), (nb095_alpha_dummy_171 f)),
        ((nb095_alpha_dummy_199 D R S_cls E), (nb095_alpha_dummy_200 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                  (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_013 D R S_cls E) from
                  (by
                    unfold nb095_alpha_dummy_013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E) 2))))
                (show f ≠ (nb095_alpha_dummy_016 f) from (by
                    unfold nb095_alpha_dummy_016;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0166 f) 2))))
                (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                      (nb095_alpha_dummy_012 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_012;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E) 1))))
                  (show f ≠ (nb095_alpha_dummy_015 f) from (by
                      unfold nb095_alpha_dummy_015;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0166 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                        (nb095_alpha_dummy_011 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_011;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E) 0))))
                    (show f ≠ (nb095_alpha_dummy_014 f) from (by
                        unfold nb095_alpha_dummy_014;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0166 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                          (nb095_alpha_dummy_017 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0165 D R S_cls E)
                                  0)))) (show f ≠ (nb095_alpha_dummy_018 f) from (by
                          unfold nb095_alpha_dummy_018;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0167 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                            (nb095_alpha_dummy_009 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_009;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0162 D R S_cls E)
                                    0)))) (show f ≠ (nb095_alpha_dummy_010 f) from (by
                            unfold nb095_alpha_dummy_010;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0163 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                              (nb095_alpha_dummy_007 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_007;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0160 D R S_cls E)
                                      0)))) (show f ≠ (nb095_alpha_dummy_008 f) from (by
                              unfold nb095_alpha_dummy_008;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0161 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                              (by decide)) dv_f_u (TAlphaVar.there
                              (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                                (by decide)) dv_f_x (TAlphaVar.here _ _ _)))))))))))))))

theorem nb095_wpp_notmem_0506 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_009 D R S_cls E) ∉ ((syn_cid)).fv := by
  simpa only [nb095_alpha_dummy_009, fv_syn_cid] using
    (nb095_compact_fv_empty_0026 D R S_cls E)

theorem nb095_wpp_notmem_0507 (f : Var) : (nb095_alpha_dummy_010 f) ∉ ((syn_cid)).fv := by
  simpa only [nb095_alpha_dummy_010, fv_syn_cid] using (nb095_compact_fv_empty_0027 f)

theorem nb095_wpp_notmem_0508 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_007 D R S_cls E) ∉ ((syn_cid)).fv := by
  simpa only [nb095_alpha_dummy_007, fv_syn_cid] using
    (nb095_compact_fv_empty_0028 D R S_cls E)

theorem nb095_wpp_notmem_0509 (f : Var) : (nb095_alpha_dummy_008 f) ∉ ((syn_cid)).fv := by
  simpa only [nb095_alpha_dummy_008, fv_syn_cid] using (nb095_compact_fv_empty_0029 f)

theorem nb095_wpp_notmem_0510 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∉ ((syn_cid)).fv := by
  simpa only [nb095_alpha_dummy_001, fv_syn_cid] using
    (nb095_compact_fv_empty_0030 D R S_cls E)

theorem nb095_wpp_notmem_0511 (u : Var) : u ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb095_compact_fv_empty_0031 u)

theorem nb095_wpp_notmem_0512 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∉ ((syn_cid)).fv := by
  simpa only [nb095_alpha_dummy_002, fv_syn_cid] using
    (nb095_compact_fv_empty_0032 D R S_cls E)

theorem nb095_wpp_notmem_0513 (x : Var) : x ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb095_compact_fv_empty_0033 x)

theorem nb095_wpp_notmem_0514 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∉ ((syn_cid)).fv := by
  simpa only [nb095_alpha_dummy_000, fv_syn_cid] using
    (nb095_compact_fv_empty_0034 D R S_cls E)

theorem nb095_wpp_notmem_0515 (f : Var) : f ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb095_compact_fv_empty_0035 f)

theorem nb095_compact_envfresh_0037 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TEnvFresh
      [((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_009 D R S_cls E) (nb095_alpha_dummy_010 f)
      (nb095_wpp_notmem_0506 D R S_cls E) (nb095_wpp_notmem_0507 f)
      (TEnvFresh.consFresh (nb095_alpha_dummy_007 D R S_cls E) (nb095_alpha_dummy_008 f)
        (nb095_wpp_notmem_0508 D R S_cls E) (nb095_wpp_notmem_0509 f)
        (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
          (nb095_wpp_notmem_0510 D R S_cls E) (nb095_wpp_notmem_0511 u)
          (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
            (nb095_wpp_notmem_0512 D R S_cls E) (nb095_wpp_notmem_0513 x)
            (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
              (nb095_wpp_notmem_0514 D R S_cls E) (nb095_wpp_notmem_0515 f)
              (TEnvFresh.nil ((syn_cid)).fv))))))

@[expose]
noncomputable def nb095_wpp_refl_0035 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TReflOn
      [((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0037 x u D R S_cls f E)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
