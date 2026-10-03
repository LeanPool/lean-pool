/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block025

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part075`. -/


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
noncomputable def nb090_split_alpha_0053 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
          (Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
          (Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                      unfold nb090_alpha_dummy_136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                  (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                      unfold nb090_alpha_dummy_138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                        unfold nb090_alpha_dummy_135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                        unfold nb090_alpha_dummy_137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                          unfold nb090_alpha_dummy_141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                          unfold nb090_alpha_dummy_142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                            unfold nb090_alpha_dummy_139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                            unfold nb090_alpha_dummy_140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                              unfold nb090_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                              unfold nb090_alpha_dummy_145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                                unfold nb090_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                                unfold nb090_alpha_dummy_146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                        unfold nb090_alpha_dummy_136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                        unfold nb090_alpha_dummy_138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                          unfold nb090_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                          unfold nb090_alpha_dummy_137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                            unfold nb090_alpha_dummy_141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                            unfold nb090_alpha_dummy_142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                              unfold nb090_alpha_dummy_139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                          (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                              unfold nb090_alpha_dummy_140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                                unfold nb090_alpha_dummy_143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                                unfold nb090_alpha_dummy_145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from
                                (by
                                  unfold nb090_alpha_dummy_144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                              (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from
                                (by
                                  unfold nb090_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part076`. -/


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
noncomputable def nb090_split_alpha_0054 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
        ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_169 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_169 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_170 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_170 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                      unfold nb090_alpha_dummy_143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                  (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                      unfold nb090_alpha_dummy_145;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                        unfold nb090_alpha_dummy_144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                    (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                        unfold nb090_alpha_dummy_146;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_169 A) from (by
                          unfold nb090_alpha_dummy_169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                      (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_170 h) from (by
                          unfold nb090_alpha_dummy_170;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_167 A) from (by
                            unfold nb090_alpha_dummy_167;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                        (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_168 h) from (by
                            unfold nb090_alpha_dummy_168;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from
                                      (by
                                        unfold nb090_alpha_dummy_150;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0136 A)
                                                1)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_153 h) from (by
                                        unfold nb090_alpha_dummy_153;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0137 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A)
                                        from (by
                                          unfold nb090_alpha_dummy_149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_152 h)
                                        from (by
                                          unfold nb090_alpha_dummy_152;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_151 A),
        (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)),
                                        ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
                                        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                        ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                        ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                                        ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                                        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                                        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)),
        ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A),
        (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
        ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A),
        (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
        ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                unfold nb090_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                unfold nb090_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                            ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                            ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                            ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                            ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                            ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                            ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                            ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                            ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                              unfold nb090_alpha_dummy_147;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                          (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                              unfold nb090_alpha_dummy_148;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                unfold nb090_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                unfold nb090_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                            ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                            ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                            ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                            ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                            ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                            ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                            ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                            ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                        unfold nb090_alpha_dummy_143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                    (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                        unfold nb090_alpha_dummy_145;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                          unfold nb090_alpha_dummy_144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                      (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                          unfold nb090_alpha_dummy_146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_169 A) from (by
                            unfold nb090_alpha_dummy_169;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                        (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_170 h) from (by
                            unfold nb090_alpha_dummy_170;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_167 A) from (by
                              unfold nb090_alpha_dummy_167;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_168 h) from (by
                              unfold nb090_alpha_dummy_168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_150 A) from (by
                                          unfold nb090_alpha_dummy_150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 1)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_153 h)
                                        from (by
                                          unfold nb090_alpha_dummy_153;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_151 A),
        (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)),
        ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A),
        (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
        ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A),
        (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                (by
                                  unfold nb090_alpha_dummy_147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                (by
                                  unfold nb090_alpha_dummy_148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                              ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                              ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                              ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                              ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                              ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                              ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                              ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                              ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                unfold nb090_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                unfold nb090_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                (by
                                  unfold nb090_alpha_dummy_147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                (by
                                  unfold nb090_alpha_dummy_148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                              ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                              ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                              ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                              ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                              ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                              ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                              ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                              ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part077`. -/


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
noncomputable def nb090_split_alpha_0055 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_177 A), (nb090_alpha_dummy_178 h)),
        ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
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
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
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
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
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
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
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
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
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
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
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
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
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
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
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
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
