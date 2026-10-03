/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part014

/-! NF weak partition development: NAR4H5C095M3Part015. -/


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
noncomputable def nb095_split_alpha_0017 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_139 D R S_cls E), (nb095_alpha_dummy_140 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_139 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_139 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_133 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_134 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_092 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_133 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_140 f))
          (Class.cab (nb095_alpha_dummy_135 f)
            (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_140 f))
            (Class.cab (nb095_alpha_dummy_135 f)
              (syn_wrex (nb095_alpha_dummy_136 f) (Class.cv (nb095_alpha_dummy_094 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_135 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_136 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                      (nb095_alpha_dummy_134 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_136 f) from (by
                      unfold nb095_alpha_dummy_136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0124 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                        (nb095_alpha_dummy_133 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_135 f) from (by
                        unfold nb095_alpha_dummy_135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0124 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                          (nb095_alpha_dummy_139 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_139;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0126 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_140 f) from (by
                          unfold nb095_alpha_dummy_140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0127 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                            (nb095_alpha_dummy_137 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_137;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0123 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_138 f) from (by
                            unfold nb095_alpha_dummy_138;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0125 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
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
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_139 D R S_cls E), (nb095_alpha_dummy_140 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
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
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_139 D R S_cls E), (nb095_alpha_dummy_140 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
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
                                    ((nb095_alpha_dummy_134 D R S_cls E),
                                      (nb095_alpha_dummy_136 f)),
                                    ((nb095_alpha_dummy_133 D R S_cls E),
                                      (nb095_alpha_dummy_135 f)),
                                    ((nb095_alpha_dummy_139 D R S_cls E),
                                      (nb095_alpha_dummy_140 f)),
                                    ((nb095_alpha_dummy_137 D R S_cls E),
                                      (nb095_alpha_dummy_138 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_013 D R S_cls E),
                                      (nb095_alpha_dummy_016 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
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
                                    ((nb095_alpha_dummy_134 D R S_cls E),
                                      (nb095_alpha_dummy_136 f)),
                                    ((nb095_alpha_dummy_133 D R S_cls E),
                                      (nb095_alpha_dummy_135 f)),
                                    ((nb095_alpha_dummy_139 D R S_cls E),
                                      (nb095_alpha_dummy_140 f)),
                                    ((nb095_alpha_dummy_137 D R S_cls E),
                                      (nb095_alpha_dummy_138 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
                                    ((nb095_alpha_dummy_013 D R S_cls E),
                                      (nb095_alpha_dummy_016 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                        (nb095_alpha_dummy_134 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_136 f) from (by
                        unfold nb095_alpha_dummy_136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0124 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                          (nb095_alpha_dummy_133 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0122 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_135 f) from (by
                          unfold nb095_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0124 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                            (nb095_alpha_dummy_139 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0126 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_140 f) from (by
                            unfold nb095_alpha_dummy_140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0127 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
                              (nb095_alpha_dummy_137 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_137;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0123 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_138 f) from (by
                              unfold nb095_alpha_dummy_138;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0125 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_094 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_134 D R S_cls E) ≠
                                (nb095_alpha_dummy_141 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_141;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0128 D R S_cls E) 0))))
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
                              (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_144 f) from
                                (by
                                  unfold nb095_alpha_dummy_144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0129 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_136 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_148 D R S_cls E) from (by
          unfold nb095_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R
                    S_cls E)
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
                  (nb095_support_mem_0133 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_141 D R S_cls E) ≠
        (nb095_alpha_dummy_145 D R S_cls E) from (by
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
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_139 D R S_cls E), (nb095_alpha_dummy_140 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_139 D R S_cls E), (nb095_alpha_dummy_140 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_149
        D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
                    D R
                    S_cls E)
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
                    S_cls
                    E)
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
                                                  (nb095_support_mem_0130 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_143 f) ≠
        (nb095_alpha_dummy_146 f) from (by
                                          unfold nb095_alpha_dummy_146;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_145 D R S_cls E),
                                        (nb095_alpha_dummy_146 f)),
                                      ((nb095_alpha_dummy_141 D R S_cls E),
                                        (nb095_alpha_dummy_143 f)),
                                      ((nb095_alpha_dummy_142 D R S_cls E),
                                        (nb095_alpha_dummy_144 f)),
                                      ((nb095_alpha_dummy_134 D R S_cls E),
                                        (nb095_alpha_dummy_136 f)),
                                      ((nb095_alpha_dummy_133 D R S_cls E),
                                        (nb095_alpha_dummy_135 f)),
                                      ((nb095_alpha_dummy_139 D R S_cls E),
                                        (nb095_alpha_dummy_140 f)),
                                      ((nb095_alpha_dummy_137 D R S_cls E),
                                        (nb095_alpha_dummy_138 f)),
                                      ((nb095_alpha_dummy_092 D R S_cls E),
                                        (nb095_alpha_dummy_094 f)),
                                      ((nb095_alpha_dummy_091 D R S_cls E),
                                        (nb095_alpha_dummy_093 f)),
                                      ((nb095_alpha_dummy_095 D R S_cls E),
                                        (nb095_alpha_dummy_096 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
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
                                                  (nb095_support_mem_0130 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_143 f) ≠
        (nb095_alpha_dummy_146 f) from (by
                                          unfold nb095_alpha_dummy_146;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_145 D R S_cls E),
                                        (nb095_alpha_dummy_146 f)),
                                      ((nb095_alpha_dummy_141 D R S_cls E),
                                        (nb095_alpha_dummy_143 f)),
                                      ((nb095_alpha_dummy_142 D R S_cls E),
                                        (nb095_alpha_dummy_144 f)),
                                      ((nb095_alpha_dummy_134 D R S_cls E),
                                        (nb095_alpha_dummy_136 f)),
                                      ((nb095_alpha_dummy_133 D R S_cls E),
                                        (nb095_alpha_dummy_135 f)),
                                      ((nb095_alpha_dummy_139 D R S_cls E),
                                        (nb095_alpha_dummy_140 f)),
                                      ((nb095_alpha_dummy_137 D R S_cls E),
                                        (nb095_alpha_dummy_138 f)),
                                      ((nb095_alpha_dummy_092 D R S_cls E),
                                        (nb095_alpha_dummy_094 f)),
                                      ((nb095_alpha_dummy_091 D R S_cls E),
                                        (nb095_alpha_dummy_093 f)),
                                      ((nb095_alpha_dummy_095 D R S_cls E),
                                        (nb095_alpha_dummy_096 f)),
                                      ((nb095_alpha_dummy_013 D R S_cls E),
                                        (nb095_alpha_dummy_016 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0018 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_167 D R S_cls E), (nb095_alpha_dummy_168 f)),
        ((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_167 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_167 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_134 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_168 f))
          (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_168 f))
            (syn_cphi (Class.cv (nb095_alpha_dummy_136 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                      (nb095_alpha_dummy_141 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_141;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E) 0))))
                  (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_143 f) from (by
                      unfold nb095_alpha_dummy_143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0129 f) 0))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                        (nb095_alpha_dummy_142 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_142;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_144 f) from (by
                        unfold nb095_alpha_dummy_144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0129 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                          (nb095_alpha_dummy_167 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0158 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_168 f) from (by
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
                                  (mem_lt_freshVar (nb095_support_mem_0156 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_166 f) from (by
                            unfold nb095_alpha_dummy_166;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_136 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_141 D R S_cls E) ≠
                                        (nb095_alpha_dummy_148 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0132 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_151 f) from
                                      (by
                                        unfold nb095_alpha_dummy_151;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0133 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_141 D R S_cls E) ≠
        (nb095_alpha_dummy_147 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0132 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_143 f) ≠
        (nb095_alpha_dummy_150 f) from (by
                                          unfold nb095_alpha_dummy_150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0133 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_145 D R S_cls E) from (by
          unfold nb095_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0130 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
          unfold nb095_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_149 D R S_cls E),
        (nb095_alpha_dummy_152 f)), ((nb095_alpha_dummy_148 D R S_cls E),
        (nb095_alpha_dummy_151 f)), ((nb095_alpha_dummy_147 D R S_cls E),
        (nb095_alpha_dummy_150 f)), ((nb095_alpha_dummy_145 D R S_cls E),
        (nb095_alpha_dummy_146 f)), ((nb095_alpha_dummy_141 D R S_cls E),
        (nb095_alpha_dummy_143 f)), ((nb095_alpha_dummy_142 D R S_cls E),
        (nb095_alpha_dummy_144 f)), ((nb095_alpha_dummy_167 D R S_cls E),
        (nb095_alpha_dummy_168 f)), ((nb095_alpha_dummy_165 D R S_cls E),
        (nb095_alpha_dummy_166 f)), ((nb095_alpha_dummy_134 D R S_cls E),
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
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
                                        ((nb095_alpha_dummy_002 D R S_cls E), x),
                                        ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_155 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_155 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_155 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠
        (nb095_alpha_dummy_155 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
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
                                        [((nb095_alpha_dummy_149 D R S_cls E),
        (nb095_alpha_dummy_152 f)), ((nb095_alpha_dummy_148 D R S_cls E),
        (nb095_alpha_dummy_151 f)), ((nb095_alpha_dummy_147 D R S_cls E),
        (nb095_alpha_dummy_150 f)), ((nb095_alpha_dummy_145 D R S_cls E),
        (nb095_alpha_dummy_146 f)), ((nb095_alpha_dummy_141 D R S_cls E),
        (nb095_alpha_dummy_143 f)), ((nb095_alpha_dummy_142 D R S_cls E),
        (nb095_alpha_dummy_144 f)), ((nb095_alpha_dummy_167 D R S_cls E),
        (nb095_alpha_dummy_168 f)), ((nb095_alpha_dummy_165 D R S_cls E),
        (nb095_alpha_dummy_166 f)), ((nb095_alpha_dummy_134 D R S_cls E),
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
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_141 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠
        (nb095_alpha_dummy_159 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
                                        (nb095_support_mem_0130 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
                                unfold nb095_alpha_dummy_146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
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
                            ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                            ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                            ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                            ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_141 D R S_cls E) ≠
                              (nb095_alpha_dummy_145 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0130 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
                              unfold nb095_alpha_dummy_146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_141 D R S_cls E) ≠
                                (nb095_alpha_dummy_145 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0130 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
                                unfold nb095_alpha_dummy_146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
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
                            ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                            ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                            ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                            ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                        (nb095_alpha_dummy_141 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_141;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_143 f) from (by
                        unfold nb095_alpha_dummy_143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0129 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_134 D R S_cls E) ≠
                          (nb095_alpha_dummy_142 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0128 D R S_cls E)
                                  1))))
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
                                  (mem_lt_freshVar (nb095_support_mem_0158 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_168 f) from (by
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
                                    (mem_lt_freshVar (nb095_support_mem_0156 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_136 f) ≠ (nb095_alpha_dummy_166 f) from (by
                              unfold nb095_alpha_dummy_166;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_134 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_136 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_141 D R S_cls E) ≠
        (nb095_alpha_dummy_148 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0132 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_143 f) ≠
        (nb095_alpha_dummy_151 f) from (by
                                          unfold nb095_alpha_dummy_151;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0133 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_141 D R S_cls E) ≠ (nb095_alpha_dummy_147 D R S_cls E) from (by
          unfold nb095_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0132 D R S_cls E)
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
                  (nb095_support_mem_0130 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
          unfold nb095_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_149 D R S_cls E),
        (nb095_alpha_dummy_152 f)), ((nb095_alpha_dummy_148 D R S_cls E),
        (nb095_alpha_dummy_151 f)), ((nb095_alpha_dummy_147 D R S_cls E),
        (nb095_alpha_dummy_150 f)), ((nb095_alpha_dummy_145 D R S_cls E),
        (nb095_alpha_dummy_146 f)), ((nb095_alpha_dummy_141 D R S_cls E),
        (nb095_alpha_dummy_143 f)), ((nb095_alpha_dummy_142 D R S_cls E),
        (nb095_alpha_dummy_144 f)), ((nb095_alpha_dummy_167 D R S_cls E),
        (nb095_alpha_dummy_168 f)), ((nb095_alpha_dummy_165 D R S_cls E),
        (nb095_alpha_dummy_166 f)), ((nb095_alpha_dummy_134 D R S_cls E),
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
        (nb095_alpha_dummy_018 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_155 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_152 f) ≠ (nb095_alpha_dummy_154 f) from (by
          unfold
            nb095_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_155 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0136
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_155 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0140
                    D R S_cls E)
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
                    D R S_cls E)
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
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_141 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_141 D R S_cls
        E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_143 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_148 D R S_cls E) ≠ (nb095_alpha_dummy_159 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0144
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_149 D R S_cls E) ≠ (nb095_alpha_dummy_161 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0148
                    D R S_cls E)
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
                    D R S_cls E)
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
                                          (nb095_support_mem_0130 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                (by
                                  unfold nb095_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
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
                              ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                              ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                              ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                              ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
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
                                        (nb095_support_mem_0130 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from (by
                                unfold nb095_alpha_dummy_146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_141 D R S_cls E) ≠
                                  (nb095_alpha_dummy_145 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_145;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0130 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_143 f) ≠ (nb095_alpha_dummy_146 f) from
                                (by
                                  unfold nb095_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_145 D R S_cls E), (nb095_alpha_dummy_146 f)),
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
                              ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
                              ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
                              ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
                              ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0019 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_175 D R S_cls E), (nb095_alpha_dummy_176 f)),
        ((nb095_alpha_dummy_173 D R S_cls E), (nb095_alpha_dummy_174 f)),
        ((nb095_alpha_dummy_013 D R S_cls E), (nb095_alpha_dummy_016 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
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
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
