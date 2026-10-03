/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C077C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part017`. -/


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
noncomputable def nb077_split_alpha_0006 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_153 F I))
          (Class.cab (nb077_alpha_dummy_147 F I)
            (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_153 F I))
            (Class.cab (nb077_alpha_dummy_147 F I)
              (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_154 x))
          (Class.cab (nb077_alpha_dummy_149 x)
            (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_154 x))
            (Class.cab (nb077_alpha_dummy_149 x)
              (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_148 F I) from (by
                      unfold nb077_alpha_dummy_148;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
                  (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_150 x) from (by
                      unfold nb077_alpha_dummy_150;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0134 x) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_147 F I) from (by
                        unfold nb077_alpha_dummy_147;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
                    (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_149 x) from (by
                        unfold nb077_alpha_dummy_149;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0134 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_153 F I) from (by
                          unfold nb077_alpha_dummy_153;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0136 F I) 0))))
                      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_154 x) from (by
                          unfold nb077_alpha_dummy_154;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0137 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_151 F I) from (by
                            unfold nb077_alpha_dummy_151;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0133 F I) 0))))
                        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_152 x) from (by
                            unfold nb077_alpha_dummy_152;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0135 x) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                  (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                    (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (by decide))
                          (freshVar_injective (((syn_cmpt x (syn_cvv)
                                  (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_143 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_155 F I) from
                            (by
                              unfold nb077_alpha_dummy_155;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                          (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_157 x) from (by
                              unfold nb077_alpha_dummy_157;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0139 x) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_156 F I) from (by
                                unfold nb077_alpha_dummy_156;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0138 F I) 1))))
                            (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_158 x) from (by
                                unfold nb077_alpha_dummy_158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0139 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_148 F I))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb077_alpha_dummy_150 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_162 F I) from
        (by
          unfold nb077_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I) 1)))) (show (nb077_alpha_dummy_157 x) ≠
        (nb077_alpha_dummy_165 x) from (by
          unfold nb077_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_161 F I) from (by
          unfold nb077_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I)
                  0)))) (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_164 x) from (by
          unfold nb077_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from (by
          unfold nb077_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I)
                  0)))) (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from (by
          unfold nb077_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_163 F I), (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I),
        (nb077_alpha_dummy_165 x)), ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)),
        ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I),
        (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
        ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
        (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_163 F I), (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I),
        (nb077_alpha_dummy_165 x)), ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)),
        ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I),
        (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
        ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
        (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_162
        F I) ≠ (nb077_alpha_dummy_173 F I) from (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_173 F I) from
        (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163
        F I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163
        F I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_159;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0140 F I) 0)))) (show
                                      (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from
                                      (by
                                        unfold nb077_alpha_dummy_160;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0141 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_159 F I),
                                      (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I),
                                      (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I),
                                      (nb077_alpha_dummy_158 x)), ((nb077_alpha_dummy_148 F I),
                                      (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
                                      (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I),
                                      (nb077_alpha_dummy_154 x)), ((nb077_alpha_dummy_151 F I),
                                      (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
                                      (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I),
                                      (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
                                      (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_159;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0140 F I)
                                              0)))) (show
                                    (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from
                                    (by
                                      unfold nb077_alpha_dummy_160;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0141 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_159;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0140 F I) 0)))) (show
                                      (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from
                                      (by
                                        unfold nb077_alpha_dummy_160;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0141 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_159 F I),
                                      (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I),
                                      (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I),
                                      (nb077_alpha_dummy_158 x)), ((nb077_alpha_dummy_148 F I),
                                      (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
                                      (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I),
                                      (nb077_alpha_dummy_154 x)), ((nb077_alpha_dummy_151 F I),
                                      (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
                                      (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I),
                                      (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I),
                                      (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
                                      (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
                                      (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I),
                                      (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
                                      (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
                                      (nb077_alpha_dummy_058 x F)),
                                    ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_148 F I) from (by
                        unfold nb077_alpha_dummy_148;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0132 F I) 1))))
                    (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_150 x) from (by
                        unfold nb077_alpha_dummy_150;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0134 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_147 F I) from (by
                          unfold nb077_alpha_dummy_147;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0132 F I) 0))))
                      (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_149 x) from (by
                          unfold nb077_alpha_dummy_149;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0134 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_153 F I) from (by
                            unfold nb077_alpha_dummy_153;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0136 F I) 0))))
                        (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_154 x) from (by
                            unfold nb077_alpha_dummy_154;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0137 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_139 F I) ≠ (nb077_alpha_dummy_151 F I) from
                            (by
                              unfold nb077_alpha_dummy_151;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0133 F I) 0))))
                          (show (nb077_alpha_dummy_142 x) ≠ (nb077_alpha_dummy_152 x) from (by
                              unfold nb077_alpha_dummy_152;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0135 x) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv)
                                    (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I))
                                      (syn_c1c)))).fv ∪ ((syn_c1st)).fv) (by decide))
                            (freshVar_injective (((syn_cmpt x (syn_cvv)
                                    (syn_cplc (Class.cv x) (syn_c1c)))).fv ∪ ((syn_c1st)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_139 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_140 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_142 x))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_143 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_155 F I) from (by
                                unfold nb077_alpha_dummy_155;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                            (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_157 x) from (by
                                unfold nb077_alpha_dummy_157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0139 x) 0))))
                            (TAlphaVar.there (show
                                (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_156 F I) from
                                (by
                                  unfold nb077_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0138 F I)
                                          1))))
                              (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_158 x) from
                                (by
                                  unfold nb077_alpha_dummy_158;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0139 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_148 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_150 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_162 F I) from (by
          unfold nb077_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I)
                  1)))) (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_165 x) from (by
          unfold nb077_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 1)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_161 F I) from (by
          unfold nb077_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I)
                  0)))) (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_164 x) from (by
          unfold nb077_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_155 F I) ≠
        (nb077_alpha_dummy_159 F I) from (by
          unfold nb077_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I)
                  0)))) (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from (by
          unfold nb077_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_163 F I), (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I),
        (nb077_alpha_dummy_165 x)), ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)),
        ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I),
        (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
        ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
        (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_163 F I), (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I),
        (nb077_alpha_dummy_165 x)), ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)),
        ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I),
        (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
        ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
        (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_157
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_162
        F I) ≠ (nb077_alpha_dummy_173 F I) from (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_173 F I) from
        (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163
        F I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163
        F I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_155 F I) ≠
        (nb077_alpha_dummy_159 F I) from (by
                                          unfold nb077_alpha_dummy_159;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0140 F I) 0)))) (show
                                        (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x)
                                        from (by
                                          unfold nb077_alpha_dummy_160;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0141 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)),
                                      ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
                                      ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
                                      ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
                                      ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
                                      ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)),
                                      ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_159;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0140 F I) 0)))) (show
                                      (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from
                                      (by
                                        unfold nb077_alpha_dummy_160;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0141 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_155 F I) ≠
        (nb077_alpha_dummy_159 F I) from (by
                                          unfold nb077_alpha_dummy_159;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0140 F I) 0)))) (show
                                        (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x)
                                        from (by
                                          unfold nb077_alpha_dummy_160;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0141 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)),
                                      ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
                                      ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
                                      ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
                                      ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
                                      ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)),
                                      ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
                                      ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                                      ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                      ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                                      ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                      ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                                      ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                      ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                                      ((nb077_alpha_dummy_057 F I),
                                        (nb077_alpha_dummy_058 x F)),
                                      ((nb077_alpha_dummy_055 F I),
                                        (nb077_alpha_dummy_056 x F)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part018`. -/


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
noncomputable def nb077_split_alpha_0007 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_181 F I), (nb077_alpha_dummy_182 x)),
        ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
        ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
        ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
        ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
        ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
        ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
        ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_181 F I))
          (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_181 F I))
            (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_182 x))
          (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_182 x))
            (syn_cphi (Class.cv (nb077_alpha_dummy_150 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_155 F I) from (by
                      unfold nb077_alpha_dummy_155;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                  (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_157 x) from (by
                      unfold nb077_alpha_dummy_157;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0139 x) 0))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_156 F I) from (by
                        unfold nb077_alpha_dummy_156;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0138 F I) 1))))
                    (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_158 x) from (by
                        unfold nb077_alpha_dummy_158;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0139 x) 1)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_181 F I) from (by
                          unfold nb077_alpha_dummy_181;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0168 F I) 0))))
                      (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_182 x) from (by
                          unfold nb077_alpha_dummy_182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0169 x) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_179 F I) from (by
                            unfold nb077_alpha_dummy_179;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0166 F I) 0))))
                        (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_180 x) from (by
                            unfold nb077_alpha_dummy_180;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0167 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_148 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_150 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_162 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_162;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0142 F I) 1)))) (show
                                      (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_165 x) from
                                      (by
                                        unfold nb077_alpha_dummy_165;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb077_support_mem_0143 x)
                                                1)))) (TAlphaVar.there (show
                                        (nb077_alpha_dummy_155 F I) ≠
        (nb077_alpha_dummy_161 F I) from (by
                                          unfold nb077_alpha_dummy_161;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0142 F I) 0)))) (show
                                        (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_164 x)
                                        from (by
                                          unfold nb077_alpha_dummy_164;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0143 x) 0))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_155 F I) ≠
        (nb077_alpha_dummy_159 F I) from (by
          unfold nb077_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I) 0)))) (show (nb077_alpha_dummy_157 x) ≠
        (nb077_alpha_dummy_160 x) from (by
          unfold nb077_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_163 F I),
        (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I), (nb077_alpha_dummy_165 x)),
                                        ((nb077_alpha_dummy_161 F I),
        (nb077_alpha_dummy_164 x)), ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)),
                                        ((nb077_alpha_dummy_155 F I),
        (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
                                        ((nb077_alpha_dummy_181 F I),
        (nb077_alpha_dummy_182 x)), ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
                                        ((nb077_alpha_dummy_148 F I),
        (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
                                        ((nb077_alpha_dummy_177 F I),
        (nb077_alpha_dummy_178 x)), ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
                                        ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                                        ((nb077_alpha_dummy_145 F I),
        (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                                        ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                                        ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                                        ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I),
        (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I),
        (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_169 F I) from (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_169 F I) from (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_169 F I) from (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb077_alpha_dummy_163 F I),
        (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I), (nb077_alpha_dummy_165 x)),
        ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)), ((nb077_alpha_dummy_159 F I),
        (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
        ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)), ((nb077_alpha_dummy_181 F I),
        (nb077_alpha_dummy_182 x)), ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
        ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
        (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_173 F I) from (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_173 F I) from (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from (by
                                unfold nb077_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                            (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from (by
                                unfold nb077_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)),
                            ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
                            ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
                            ((nb077_alpha_dummy_181 F I), (nb077_alpha_dummy_182 x)),
                            ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
                            ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
                            ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
                            ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)),
                            ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
                            ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                            ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                            ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from
                            (by
                              unfold nb077_alpha_dummy_159;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                          (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from (by
                              unfold nb077_alpha_dummy_160;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from (by
                                unfold nb077_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                            (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from (by
                                unfold nb077_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)),
                            ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
                            ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
                            ((nb077_alpha_dummy_181 F I), (nb077_alpha_dummy_182 x)),
                            ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
                            ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
                            ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
                            ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)),
                            ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
                            ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                            ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                            ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                            ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                            ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                            ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                            ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                            ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                            ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_155 F I) from (by
                        unfold nb077_alpha_dummy_155;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0138 F I) 0))))
                    (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_157 x) from (by
                        unfold nb077_alpha_dummy_157;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0139 x) 0)))) (TAlphaVar.there
                      (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_156 F I) from (by
                          unfold nb077_alpha_dummy_156;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0138 F I) 1))))
                      (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_158 x) from (by
                          unfold nb077_alpha_dummy_158;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0139 x) 1))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_181 F I) from (by
                            unfold nb077_alpha_dummy_181;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0168 F I) 0))))
                        (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_182 x) from (by
                            unfold nb077_alpha_dummy_182;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0169 x) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_148 F I) ≠ (nb077_alpha_dummy_179 F I) from
                            (by
                              unfold nb077_alpha_dummy_179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0166 F I) 0))))
                          (show (nb077_alpha_dummy_150 x) ≠ (nb077_alpha_dummy_180 x) from (by
                              unfold nb077_alpha_dummy_180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0167 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_148 F I))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_150 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb077_alpha_dummy_155 F I) ≠
        (nb077_alpha_dummy_162 F I) from (by
                                          unfold nb077_alpha_dummy_162;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0142 F I) 1)))) (show
                                        (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_165 x)
                                        from (by
                                          unfold nb077_alpha_dummy_165;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0143 x) 1))))
                                      (TAlphaVar.there (show (nb077_alpha_dummy_155 F I) ≠
        (nb077_alpha_dummy_161 F I) from (by
          unfold nb077_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0142 F I) 0)))) (show (nb077_alpha_dummy_157 x) ≠
        (nb077_alpha_dummy_164 x) from (by
          unfold nb077_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0143 x) 0)))) (TAlphaVar.there (show
        (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from (by
          unfold nb077_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0140 F I) 0)))) (show (nb077_alpha_dummy_157 x) ≠
        (nb077_alpha_dummy_160 x) from (by
          unfold nb077_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0141 x) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb077_alpha_dummy_163 F I),
        (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I), (nb077_alpha_dummy_165 x)),
        ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)), ((nb077_alpha_dummy_159 F I),
        (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
        ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)), ((nb077_alpha_dummy_181 F I),
        (nb077_alpha_dummy_182 x)), ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
        ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I),
        (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)),
        ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I),
        (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
        ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I),
        (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
        ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I),
        (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
        ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_162 F
        I) ≠ (nb077_alpha_dummy_169 F I) from (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0146
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0144
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠ (nb077_alpha_dummy_169 F I) from
        (by
          unfold
            nb077_alpha_dummy_169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0150
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_170 x) from (by
          unfold
            nb077_alpha_dummy_170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_167 F I) from (by
          unfold
            nb077_alpha_dummy_167;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0148
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_168 x) from (by
          unfold
            nb077_alpha_dummy_168;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_163 F I), (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I),
        (nb077_alpha_dummy_165 x)), ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)),
        ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I),
        (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
        ((nb077_alpha_dummy_181 F I), (nb077_alpha_dummy_182 x)), ((nb077_alpha_dummy_179 F I),
        (nb077_alpha_dummy_180 x)), ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
        ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_177 F I),
        (nb077_alpha_dummy_178 x)), ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
        ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I),
        (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
        ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I),
        (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
        ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I),
        (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I),
        (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I),
        (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I),
        (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I),
        (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I),
        (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I),
        (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I),
        (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I),
        (nb077_alpha_dummy_005 x F I))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_155 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_162 F
        I) ≠ (nb077_alpha_dummy_173 F I) from (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠ (nb077_alpha_dummy_173 F I) from
        (by
          unfold
            nb077_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0154
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_174 x) from (by
          unfold
            nb077_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0155
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_162 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0152
                    F I)
                  0)))) (show (nb077_alpha_dummy_165 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0153
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_155
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_157 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163 F
        I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_163 F
        I) ≠ (nb077_alpha_dummy_175 F I) from (by
          unfold
            nb077_alpha_dummy_175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0158
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_176 x) from (by
          unfold
            nb077_alpha_dummy_176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0159
                    x)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_163 F I) ≠
        (nb077_alpha_dummy_171 F I) from (by
          unfold
            nb077_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0156
                    F I)
                  0)))) (show (nb077_alpha_dummy_166 x) ≠ (nb077_alpha_dummy_172 x) from (by
          unfold
            nb077_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0157
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from
                                (by
                                  unfold nb077_alpha_dummy_159;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0140 F I)
                                          0))))
                              (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from
                                (by
                                  unfold nb077_alpha_dummy_160;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)),
                              ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
                              ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
                              ((nb077_alpha_dummy_181 F I), (nb077_alpha_dummy_182 x)),
                              ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
                              ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
                              ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
                              ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)),
                              ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
                              ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                              ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                              ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                              ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from (by
                                unfold nb077_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0140 F I) 0))))
                            (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from (by
                                unfold nb077_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb077_alpha_dummy_155 F I) ≠ (nb077_alpha_dummy_159 F I) from
                                (by
                                  unfold nb077_alpha_dummy_159;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0140 F I)
                                          0))))
                              (show (nb077_alpha_dummy_157 x) ≠ (nb077_alpha_dummy_160 x) from
                                (by
                                  unfold nb077_alpha_dummy_160;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0141 x) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)),
                              ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)),
                              ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)),
                              ((nb077_alpha_dummy_181 F I), (nb077_alpha_dummy_182 x)),
                              ((nb077_alpha_dummy_179 F I), (nb077_alpha_dummy_180 x)),
                              ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)),
                              ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)),
                              ((nb077_alpha_dummy_177 F I), (nb077_alpha_dummy_178 x)),
                              ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)),
                              ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)),
                              ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)),
                              ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)),
                              ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)),
                              ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)),
                              ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)),
                              ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)),
                              ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)),
                              ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)),
                              ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
                              ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
                              ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
                              ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
                              ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
                              ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
                              ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part019`. -/


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

theorem nb077_compact_fv_empty_0160 (F : Class) (I : Class) :
    (nb077_alpha_dummy_141 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0161 (x : Var) :
    (nb077_alpha_dummy_144 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
