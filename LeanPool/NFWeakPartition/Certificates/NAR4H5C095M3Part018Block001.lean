/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part017

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `AlphaSupport.NAR4H5C095M3Part018Stage1`. -/


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
noncomputable def nb095_split_alpha_0026 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_165 D R S_cls E))
          (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_165 D R S_cls E))
            (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_166 f))
          (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_166 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                              (nb095_alpha_dummy_141 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_141;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_143 f) from (by
                              unfold nb095_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0129 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                                (nb095_alpha_dummy_142 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_142;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0128 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_144 f) from (by
                                unfold nb095_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0129 f) 1))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                                  (nb095_alpha_dummy_167 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_167;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0158 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_168 f) from
                                (by
                                  unfold nb095_alpha_dummy_168;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0159 f) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                                    (nb095_alpha_dummy_165 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_165;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0156 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_166 f) from (by
                                    unfold nb095_alpha_dummy_166;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0157 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_136 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_141 D R S_cls E) ≠
        (nb095_alpha_dummy_148 D R S_cls E) from (by
          unfold nb095_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_151 f) from (by
          unfold nb095_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_147 D R S_cls E) from (by
          unfold nb095_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_150 f) from (by
          unfold nb095_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_145 D R S_cls E) from (by
          unfold nb095_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0130 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
          unfold nb095_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_149 D R S_cls E), (nb095_alpha_dummy_152 f)),
        ((nb095_alpha_dummy_148 D R S_cls E), (nb095_alpha_dummy_151 f)),
        ((nb095_alpha_dummy_147 D R S_cls E), (nb095_alpha_dummy_150 f)),
        ((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
        ((nb095_alpha_dummy_141 D R S_cls E), (nb095_alpha_dummy_143 f)),
        ((nb095_alpha_dummy_142 D R S_cls E), (nb095_alpha_dummy_144 f)),
        ((nb095_alpha_dummy_167 D R S_cls E), (nb095_alpha_dummy_168 f)),
        ((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_148
        D R S_cls E) ≠ (nb095_alpha_dummy_155 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_149 D R S_cls E), (nb095_alpha_dummy_152 f)),
        ((nb095_alpha_dummy_148 D R S_cls E), (nb095_alpha_dummy_151 f)),
        ((nb095_alpha_dummy_147 D R S_cls E), (nb095_alpha_dummy_150 f)),
        ((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
        ((nb095_alpha_dummy_141 D R S_cls E), (nb095_alpha_dummy_143 f)),
        ((nb095_alpha_dummy_142 D R S_cls E), (nb095_alpha_dummy_144 f)),
        ((nb095_alpha_dummy_167 D R S_cls E), (nb095_alpha_dummy_168 f)),
        ((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_160 f) from (by
          unfold
            nb095_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_160 f) from (by
          unfold
            nb095_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_149
        D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_162 f) from (by
          unfold
            nb095_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_149
        D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_162 f) from (by
          unfold
            nb095_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_141 D R S_cls E) ≠
                                        (nb095_alpha_dummy_145 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                      (by
                                        unfold nb095_alpha_dummy_146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_145 D R S_cls E),
                                      (nb095_alpha_dummy_146 f)),
                                    ((nb095_alpha_dummy_141 D R S_cls E),
                                      (nb095_alpha_dummy_143 f)),
                                    ((nb095_alpha_dummy_142 D R S_cls E),
                                      (nb095_alpha_dummy_144 f)),
                                    ((nb095_alpha_dummy_167 D R S_cls E),
                                      (nb095_alpha_dummy_168 f)),
                                    ((nb095_alpha_dummy_165 D R S_cls E),
                                      (nb095_alpha_dummy_166 f)),
                                    ((nb095_alpha_dummy_134 D R S_cls E),
                                      (nb095_alpha_dummy_136 f)),
                                    ((nb095_alpha_dummy_133 D R S_cls E),
                                      (nb095_alpha_dummy_135 f)),
                                    ((nb095_alpha_dummy_163 D R S_cls E),
                                      (nb095_alpha_dummy_164 f)),
                                    ((nb095_alpha_dummy_137 D R S_cls E),
                                      (nb095_alpha_dummy_138 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_206 D R S_cls E),
                                      (nb095_alpha_dummy_208 f)),
                                    ((nb095_alpha_dummy_205 D R S_cls E),
                                      (nb095_alpha_dummy_207 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_141 D R S_cls E) ≠
                                      (nb095_alpha_dummy_145 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_145;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                    (by
                                      unfold nb095_alpha_dummy_146;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0131 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_141 D R S_cls E) ≠
                                        (nb095_alpha_dummy_145 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                      (by
                                        unfold nb095_alpha_dummy_146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_145 D R S_cls E),
                                      (nb095_alpha_dummy_146 f)),
                                    ((nb095_alpha_dummy_141 D R S_cls E),
                                      (nb095_alpha_dummy_143 f)),
                                    ((nb095_alpha_dummy_142 D R S_cls E),
                                      (nb095_alpha_dummy_144 f)),
                                    ((nb095_alpha_dummy_167 D R S_cls E),
                                      (nb095_alpha_dummy_168 f)),
                                    ((nb095_alpha_dummy_165 D R S_cls E),
                                      (nb095_alpha_dummy_166 f)),
                                    ((nb095_alpha_dummy_134 D R S_cls E),
                                      (nb095_alpha_dummy_136 f)),
                                    ((nb095_alpha_dummy_133 D R S_cls E),
                                      (nb095_alpha_dummy_135 f)),
                                    ((nb095_alpha_dummy_163 D R S_cls E),
                                      (nb095_alpha_dummy_164 f)),
                                    ((nb095_alpha_dummy_137 D R S_cls E),
                                      (nb095_alpha_dummy_138 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_206 D R S_cls E),
                                      (nb095_alpha_dummy_208 f)),
                                    ((nb095_alpha_dummy_205 D R S_cls E),
                                      (nb095_alpha_dummy_207 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                              (nb095_alpha_dummy_141 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_141;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_143 f) from (by
                              unfold nb095_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0129 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                                (nb095_alpha_dummy_142 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_142;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0128 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_144 f) from (by
                                unfold nb095_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0129 f) 1))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                                  (nb095_alpha_dummy_167 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_167;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0158 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_168 f) from
                                (by
                                  unfold nb095_alpha_dummy_168;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0159 f) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                                    (nb095_alpha_dummy_165 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_165;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0156 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_166 f) from (by
                                    unfold nb095_alpha_dummy_166;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0157 f)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_136 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_141 D R S_cls E) ≠
        (nb095_alpha_dummy_148 D R S_cls E) from (by
          unfold nb095_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_151 f) from (by
          unfold nb095_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_147 D R S_cls E) from (by
          unfold nb095_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_150 f) from (by
          unfold nb095_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_145 D R S_cls E) from (by
          unfold nb095_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0130 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
          unfold nb095_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_149 D R S_cls E), (nb095_alpha_dummy_152 f)),
        ((nb095_alpha_dummy_148 D R S_cls E), (nb095_alpha_dummy_151 f)),
        ((nb095_alpha_dummy_147 D R S_cls E), (nb095_alpha_dummy_150 f)),
        ((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
        ((nb095_alpha_dummy_141 D R S_cls E), (nb095_alpha_dummy_143 f)),
        ((nb095_alpha_dummy_142 D R S_cls E), (nb095_alpha_dummy_144 f)),
        ((nb095_alpha_dummy_167 D R S_cls E), (nb095_alpha_dummy_168 f)),
        ((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_148
        D R S_cls E) ≠ (nb095_alpha_dummy_155 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0134
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_156 f) from (by
          unfold
            nb095_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_153 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0138
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_149 D R S_cls E), (nb095_alpha_dummy_152 f)),
        ((nb095_alpha_dummy_148 D R S_cls E), (nb095_alpha_dummy_151 f)),
        ((nb095_alpha_dummy_147 D R S_cls E), (nb095_alpha_dummy_150 f)),
        ((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
        ((nb095_alpha_dummy_141 D R S_cls E), (nb095_alpha_dummy_143 f)),
        ((nb095_alpha_dummy_142 D R S_cls E), (nb095_alpha_dummy_144 f)),
        ((nb095_alpha_dummy_167 D R S_cls E), (nb095_alpha_dummy_168 f)),
        ((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
        ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_160 f) from (by
          unfold
            nb095_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_160 f) from (by
          unfold
            nb095_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0142
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_151 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_149
        D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_162 f) from (by
          unfold
            nb095_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_149
        D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_162 f) from (by
          unfold
            nb095_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_157 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0146
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_158 f) from (by
          unfold
            nb095_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_141 D R S_cls E) ≠
                                        (nb095_alpha_dummy_145 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                      (by
                                        unfold nb095_alpha_dummy_146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_145 D R S_cls E),
                                      (nb095_alpha_dummy_146 f)),
                                    ((nb095_alpha_dummy_141 D R S_cls E),
                                      (nb095_alpha_dummy_143 f)),
                                    ((nb095_alpha_dummy_142 D R S_cls E),
                                      (nb095_alpha_dummy_144 f)),
                                    ((nb095_alpha_dummy_167 D R S_cls E),
                                      (nb095_alpha_dummy_168 f)),
                                    ((nb095_alpha_dummy_165 D R S_cls E),
                                      (nb095_alpha_dummy_166 f)),
                                    ((nb095_alpha_dummy_134 D R S_cls E),
                                      (nb095_alpha_dummy_136 f)),
                                    ((nb095_alpha_dummy_133 D R S_cls E),
                                      (nb095_alpha_dummy_135 f)),
                                    ((nb095_alpha_dummy_163 D R S_cls E),
                                      (nb095_alpha_dummy_164 f)),
                                    ((nb095_alpha_dummy_137 D R S_cls E),
                                      (nb095_alpha_dummy_138 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_206 D R S_cls E),
                                      (nb095_alpha_dummy_208 f)),
                                    ((nb095_alpha_dummy_205 D R S_cls E),
                                      (nb095_alpha_dummy_207 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_141 D R S_cls E) ≠
                                      (nb095_alpha_dummy_145 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_145;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                    (by
                                      unfold nb095_alpha_dummy_146;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0131 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_141 D R S_cls E) ≠
                                        (nb095_alpha_dummy_145 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_145;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0130 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                      (by
                                        unfold nb095_alpha_dummy_146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_145 D R S_cls E),
                                      (nb095_alpha_dummy_146 f)),
                                    ((nb095_alpha_dummy_141 D R S_cls E),
                                      (nb095_alpha_dummy_143 f)),
                                    ((nb095_alpha_dummy_142 D R S_cls E),
                                      (nb095_alpha_dummy_144 f)),
                                    ((nb095_alpha_dummy_167 D R S_cls E),
                                      (nb095_alpha_dummy_168 f)),
                                    ((nb095_alpha_dummy_165 D R S_cls E),
                                      (nb095_alpha_dummy_166 f)),
                                    ((nb095_alpha_dummy_134 D R S_cls E),
                                      (nb095_alpha_dummy_136 f)),
                                    ((nb095_alpha_dummy_133 D R S_cls E),
                                      (nb095_alpha_dummy_135 f)),
                                    ((nb095_alpha_dummy_163 D R S_cls E),
                                      (nb095_alpha_dummy_164 f)),
                                    ((nb095_alpha_dummy_137 D R S_cls E),
                                      (nb095_alpha_dummy_138 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_206 D R S_cls E),
                                      (nb095_alpha_dummy_208 f)),
                                    ((nb095_alpha_dummy_205 D R S_cls E),
                                      (nb095_alpha_dummy_207 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed
          [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
            ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
            ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
            ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
            ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
            ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
            ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
            ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
            ((nb095_alpha_dummy_206 D R S_cls E), (nb095_alpha_dummy_208 f)),
            ((nb095_alpha_dummy_205 D R S_cls E), (nb095_alpha_dummy_207 f)),
            ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
            ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb095_focused_notmem_0005 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_247 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0006 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_248 x D R) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb095_focused_notmem_0007 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_245 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cnin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0008 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_246 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0009 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb095_compact_envfresh_0095 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_247 D R S_cls E) (nb095_alpha_dummy_248 x D R)
      (nb095_focused_notmem_0005 D R S_cls E) (nb095_focused_notmem_0006 x D R)
      (TEnvFresh.consFresh (nb095_alpha_dummy_245 D R S_cls E)
        (nb095_alpha_dummy_246 x D R) (nb095_focused_notmem_0007 D R S_cls E)
        (nb095_focused_notmem_0008 x D R)
        (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
          (nb095_focused_notmem_0009 D R S_cls E) dv_D_u
          (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
            (nb095_focused_notmem_0000 D R S_cls E) dv_D_x
            (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
              (nb095_focused_notmem_0001 D R S_cls E) dv_D_f (TEnvFresh.nil D.fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C095M3Part018Stage2`. -/


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
noncomputable def nb095_focused_refl_0002 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) :
    TReflOn
      [((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      D.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0095 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)

theorem nb095_compact_fv_empty_0204 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_250 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0205 (x : Var) (R : Class) :
    (nb095_alpha_dummy_252 x R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0206 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_249 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0207 (x : Var) (R : Class) :
    (nb095_alpha_dummy_251 x R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0208 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_247 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0209 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_248 x D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0210 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_245 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0211 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_246 x D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
