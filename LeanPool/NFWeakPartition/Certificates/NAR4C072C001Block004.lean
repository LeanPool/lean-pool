/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C072C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C072C001Part014`. -/


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
noncomputable def nb072_split_alpha_0005 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) :
    TAlphaWff
      [((nb072_alpha_dummy_158 A B R S_cls H), (nb072_alpha_dummy_159 y H)),
        ((nb072_alpha_dummy_156 A B R S_cls H), (nb072_alpha_dummy_157 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_154 A B R S_cls H), (nb072_alpha_dummy_155 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_158 A B R S_cls H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H)))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_158 A B R S_cls H))
            (syn_cphi (Class.cv (nb072_alpha_dummy_125 A B R S_cls H))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_159 y H))
          (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))) (Wff.neg
          (Wff.classMem (Class.cv (nb072_alpha_dummy_159 y H))
            (syn_cphi (Class.cv (nb072_alpha_dummy_127 y H)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                      (nb072_alpha_dummy_132 A B R S_cls H) from (by
                      unfold nb072_alpha_dummy_132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0130 A B R S_cls H) 0))))
                  (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_134 y H) from (by
                      unfold nb072_alpha_dummy_134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb072_support_mem_0131 y H) 0)))) (TAlphaVar.there
                    (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                        (nb072_alpha_dummy_133 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0130 A B R S_cls H)
                                1))))
                    (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_135 y H) from (by
                        unfold nb072_alpha_dummy_135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0131 y H) 1))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                          (nb072_alpha_dummy_158 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_158;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0160 A B R S_cls H)
                                  0))))
                      (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_159 y H) from (by
                          unfold nb072_alpha_dummy_159;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0161 y H) 0))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                            (nb072_alpha_dummy_156 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_156;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0158 A B R S_cls H)
                                    0))))
                        (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_157 y H) from (by
                            unfold nb072_alpha_dummy_157;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0159 y H) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb072_alpha_dummy_127 y H))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_139 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_139;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0134 A B R S_cls H)
                                                1)))) (show (nb072_alpha_dummy_134 y H) ≠
                                        (nb072_alpha_dummy_142 y H) from (by
                                        unfold nb072_alpha_dummy_142;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0135 y H) 1))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_138 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0134 A B R S_cls H)
                                                  0)))) (show (nb072_alpha_dummy_134 y H) ≠
        (nb072_alpha_dummy_141 y H) from (by
                                          unfold nb072_alpha_dummy_141;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0135 y H) 0))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_132 A B R S_cls H) ≠ (nb072_alpha_dummy_136 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0132 A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from (by
          unfold nb072_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0133 y H) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb072_alpha_dummy_140 A B R S_cls H),
        (nb072_alpha_dummy_143 y H)), ((nb072_alpha_dummy_139 A B R S_cls H),
        (nb072_alpha_dummy_142 y H)), ((nb072_alpha_dummy_138 A B R S_cls H),
        (nb072_alpha_dummy_141 y H)), ((nb072_alpha_dummy_136 A B R S_cls H),
        (nb072_alpha_dummy_137 y H)), ((nb072_alpha_dummy_132 A B R S_cls H),
        (nb072_alpha_dummy_134 y H)), ((nb072_alpha_dummy_133 A B R S_cls H),
        (nb072_alpha_dummy_135 y H)), ((nb072_alpha_dummy_158 A B R S_cls H),
        (nb072_alpha_dummy_159 y H)), ((nb072_alpha_dummy_156 A B R S_cls H),
        (nb072_alpha_dummy_157 y H)), ((nb072_alpha_dummy_125 A B R S_cls H),
        (nb072_alpha_dummy_127 y H)), ((nb072_alpha_dummy_124 A B R S_cls H),
        (nb072_alpha_dummy_126 y H)), ((nb072_alpha_dummy_154 A B R S_cls H),
        (nb072_alpha_dummy_155 y H)), ((nb072_alpha_dummy_128 A B R S_cls H),
        (nb072_alpha_dummy_129 y H)), ((nb072_alpha_dummy_116 A B R S_cls H),
        (nb072_alpha_dummy_117 y H)), ((nb072_alpha_dummy_118 A B R S_cls H),
        (nb072_alpha_dummy_119 y H)), ((nb072_alpha_dummy_121 A B R S_cls H),
        (nb072_alpha_dummy_123 y H)), ((nb072_alpha_dummy_120 A B R S_cls H),
        (nb072_alpha_dummy_122 y H)), ((nb072_alpha_dummy_039 A B R S_cls H),
        (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H),
        (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_114 A B R S_cls H),
        (nb072_alpha_dummy_115 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H),
        (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y),
                                        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb072_alpha_dummy_140 A B R S_cls H),
        (nb072_alpha_dummy_143 y H)), ((nb072_alpha_dummy_139 A B R S_cls H),
        (nb072_alpha_dummy_142 y H)), ((nb072_alpha_dummy_138 A B R S_cls H),
        (nb072_alpha_dummy_141 y H)), ((nb072_alpha_dummy_136 A B R S_cls H),
        (nb072_alpha_dummy_137 y H)), ((nb072_alpha_dummy_132 A B R S_cls H),
        (nb072_alpha_dummy_134 y H)), ((nb072_alpha_dummy_133 A B R S_cls H),
        (nb072_alpha_dummy_135 y H)), ((nb072_alpha_dummy_158 A B R S_cls H),
        (nb072_alpha_dummy_159 y H)), ((nb072_alpha_dummy_156 A B R S_cls H),
        (nb072_alpha_dummy_157 y H)), ((nb072_alpha_dummy_125 A B R S_cls H),
        (nb072_alpha_dummy_127 y H)), ((nb072_alpha_dummy_124 A B R S_cls H),
        (nb072_alpha_dummy_126 y H)), ((nb072_alpha_dummy_154 A B R S_cls H),
        (nb072_alpha_dummy_155 y H)), ((nb072_alpha_dummy_128 A B R S_cls H),
        (nb072_alpha_dummy_129 y H)), ((nb072_alpha_dummy_116 A B R S_cls H),
        (nb072_alpha_dummy_117 y H)), ((nb072_alpha_dummy_118 A B R S_cls H),
        (nb072_alpha_dummy_119 y H)), ((nb072_alpha_dummy_121 A B R S_cls H),
        (nb072_alpha_dummy_123 y H)), ((nb072_alpha_dummy_120 A B R S_cls H),
        (nb072_alpha_dummy_122 y H)), ((nb072_alpha_dummy_039 A B R S_cls H),
        (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H),
        (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_114 A B R S_cls H),
        (nb072_alpha_dummy_115 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H),
        (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_c0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_150 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_150 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_136;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0132 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from (by
                                unfold nb072_alpha_dummy_137;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0133 y H) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb072_alpha_dummy_136 A B R S_cls H), (nb072_alpha_dummy_137 y H)),
                            ((nb072_alpha_dummy_132 A B R S_cls H),
                              (nb072_alpha_dummy_134 y H)),
                            ((nb072_alpha_dummy_133 A B R S_cls H),
                              (nb072_alpha_dummy_135 y H)),
                            ((nb072_alpha_dummy_158 A B R S_cls H),
                              (nb072_alpha_dummy_159 y H)),
                            ((nb072_alpha_dummy_156 A B R S_cls H),
                              (nb072_alpha_dummy_157 y H)),
                            ((nb072_alpha_dummy_125 A B R S_cls H),
                              (nb072_alpha_dummy_127 y H)),
                            ((nb072_alpha_dummy_124 A B R S_cls H),
                              (nb072_alpha_dummy_126 y H)),
                            ((nb072_alpha_dummy_154 A B R S_cls H),
                              (nb072_alpha_dummy_155 y H)),
                            ((nb072_alpha_dummy_128 A B R S_cls H),
                              (nb072_alpha_dummy_129 y H)),
                            ((nb072_alpha_dummy_116 A B R S_cls H),
                              (nb072_alpha_dummy_117 y H)),
                            ((nb072_alpha_dummy_118 A B R S_cls H),
                              (nb072_alpha_dummy_119 y H)),
                            ((nb072_alpha_dummy_121 A B R S_cls H),
                              (nb072_alpha_dummy_123 y H)),
                            ((nb072_alpha_dummy_120 A B R S_cls H),
                              (nb072_alpha_dummy_122 y H)),
                            ((nb072_alpha_dummy_039 A B R S_cls H),
                              (nb072_alpha_dummy_041 x y H)),
                            ((nb072_alpha_dummy_038 A B R S_cls H),
                              (nb072_alpha_dummy_040 x y H)),
                            ((nb072_alpha_dummy_114 A B R S_cls H),
                              (nb072_alpha_dummy_115 x y H)),
                            ((nb072_alpha_dummy_042 A B R S_cls H),
                              (nb072_alpha_dummy_043 x y H)),
                            ((nb072_alpha_dummy_001 A B R S_cls H), y),
                            ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb072_alpha_dummy_132 A B R S_cls H) ≠
                              (nb072_alpha_dummy_136 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0132 A B R S_cls H) 0))))
                          (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from
                            (by
                              unfold nb072_alpha_dummy_137;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0133 y H) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_136;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0132 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from (by
                                unfold nb072_alpha_dummy_137;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0133 y H) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb072_alpha_dummy_136 A B R S_cls H), (nb072_alpha_dummy_137 y H)),
                            ((nb072_alpha_dummy_132 A B R S_cls H),
                              (nb072_alpha_dummy_134 y H)),
                            ((nb072_alpha_dummy_133 A B R S_cls H),
                              (nb072_alpha_dummy_135 y H)),
                            ((nb072_alpha_dummy_158 A B R S_cls H),
                              (nb072_alpha_dummy_159 y H)),
                            ((nb072_alpha_dummy_156 A B R S_cls H),
                              (nb072_alpha_dummy_157 y H)),
                            ((nb072_alpha_dummy_125 A B R S_cls H),
                              (nb072_alpha_dummy_127 y H)),
                            ((nb072_alpha_dummy_124 A B R S_cls H),
                              (nb072_alpha_dummy_126 y H)),
                            ((nb072_alpha_dummy_154 A B R S_cls H),
                              (nb072_alpha_dummy_155 y H)),
                            ((nb072_alpha_dummy_128 A B R S_cls H),
                              (nb072_alpha_dummy_129 y H)),
                            ((nb072_alpha_dummy_116 A B R S_cls H),
                              (nb072_alpha_dummy_117 y H)),
                            ((nb072_alpha_dummy_118 A B R S_cls H),
                              (nb072_alpha_dummy_119 y H)),
                            ((nb072_alpha_dummy_121 A B R S_cls H),
                              (nb072_alpha_dummy_123 y H)),
                            ((nb072_alpha_dummy_120 A B R S_cls H),
                              (nb072_alpha_dummy_122 y H)),
                            ((nb072_alpha_dummy_039 A B R S_cls H),
                              (nb072_alpha_dummy_041 x y H)),
                            ((nb072_alpha_dummy_038 A B R S_cls H),
                              (nb072_alpha_dummy_040 x y H)),
                            ((nb072_alpha_dummy_114 A B R S_cls H),
                              (nb072_alpha_dummy_115 x y H)),
                            ((nb072_alpha_dummy_042 A B R S_cls H),
                              (nb072_alpha_dummy_043 x y H)),
                            ((nb072_alpha_dummy_001 A B R S_cls H), y),
                            ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                        (nb072_alpha_dummy_132 A B R S_cls H) from (by
                        unfold nb072_alpha_dummy_132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0130 A B R S_cls H)
                                0))))
                    (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_134 y H) from (by
                        unfold nb072_alpha_dummy_134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb072_support_mem_0131 y H) 0))))
                    (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                          (nb072_alpha_dummy_133 A B R S_cls H) from (by
                          unfold nb072_alpha_dummy_133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0130 A B R S_cls H)
                                  1))))
                      (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_135 y H) from (by
                          unfold nb072_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb072_support_mem_0131 y H) 1))))
                      (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                            (nb072_alpha_dummy_158 A B R S_cls H) from (by
                            unfold nb072_alpha_dummy_158;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0160 A B R S_cls H)
                                    0))))
                        (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_159 y H) from (by
                            unfold nb072_alpha_dummy_159;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb072_support_mem_0161 y H) 0))))
                        (TAlphaVar.there (show (nb072_alpha_dummy_125 A B R S_cls H) ≠
                              (nb072_alpha_dummy_156 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_156;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0158 A B R S_cls H) 0))))
                          (show (nb072_alpha_dummy_127 y H) ≠ (nb072_alpha_dummy_157 y H) from
                            (by
                              unfold nb072_alpha_dummy_157;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0159 y H) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb072_alpha_dummy_125 A B R S_cls H))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb072_alpha_dummy_127 y H))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_132 A B R S_cls H) ≠
        (nb072_alpha_dummy_139 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_139;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0134 A B R S_cls H)
                                                  1)))) (show (nb072_alpha_dummy_134 y H) ≠
        (nb072_alpha_dummy_142 y H) from (by
                                          unfold nb072_alpha_dummy_142;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0135 y H) 1))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_132 A B R S_cls H) ≠ (nb072_alpha_dummy_138 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0134 A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_141 y H) from (by
          unfold nb072_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0135 y H) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_132 A B R S_cls H) ≠ (nb072_alpha_dummy_136 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0132 A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from (by
          unfold nb072_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0133 y H) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb072_alpha_dummy_140 A B R S_cls H),
        (nb072_alpha_dummy_143 y H)), ((nb072_alpha_dummy_139 A B R S_cls H),
        (nb072_alpha_dummy_142 y H)), ((nb072_alpha_dummy_138 A B R S_cls H),
        (nb072_alpha_dummy_141 y H)), ((nb072_alpha_dummy_136 A B R S_cls H),
        (nb072_alpha_dummy_137 y H)), ((nb072_alpha_dummy_132 A B R S_cls H),
        (nb072_alpha_dummy_134 y H)), ((nb072_alpha_dummy_133 A B R S_cls H),
        (nb072_alpha_dummy_135 y H)), ((nb072_alpha_dummy_158 A B R S_cls H),
        (nb072_alpha_dummy_159 y H)), ((nb072_alpha_dummy_156 A B R S_cls H),
        (nb072_alpha_dummy_157 y H)), ((nb072_alpha_dummy_125 A B R S_cls H),
        (nb072_alpha_dummy_127 y H)), ((nb072_alpha_dummy_124 A B R S_cls H),
        (nb072_alpha_dummy_126 y H)), ((nb072_alpha_dummy_154 A B R S_cls H),
        (nb072_alpha_dummy_155 y H)), ((nb072_alpha_dummy_128 A B R S_cls H),
        (nb072_alpha_dummy_129 y H)), ((nb072_alpha_dummy_116 A B R S_cls H),
        (nb072_alpha_dummy_117 y H)), ((nb072_alpha_dummy_118 A B R S_cls H),
        (nb072_alpha_dummy_119 y H)), ((nb072_alpha_dummy_121 A B R S_cls H),
        (nb072_alpha_dummy_123 y H)), ((nb072_alpha_dummy_120 A B R S_cls H),
        (nb072_alpha_dummy_122 y H)), ((nb072_alpha_dummy_039 A B R S_cls H),
        (nb072_alpha_dummy_041 x y H)), ((nb072_alpha_dummy_038 A B R S_cls H),
        (nb072_alpha_dummy_040 x y H)), ((nb072_alpha_dummy_114 A B R S_cls H),
        (nb072_alpha_dummy_115 x y H)), ((nb072_alpha_dummy_042 A B R S_cls H),
        (nb072_alpha_dummy_043 x y H)), ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0138
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0139
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0136
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0137
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_146 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0142
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_147 y H) from (by
          unfold
            nb072_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0143
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_144 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0140
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_145 y H) from (by
          unfold
            nb072_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0141
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_140 A B R S_cls H), (nb072_alpha_dummy_143 y H)),
        ((nb072_alpha_dummy_139 A B R S_cls H), (nb072_alpha_dummy_142 y H)),
        ((nb072_alpha_dummy_138 A B R S_cls H), (nb072_alpha_dummy_141 y H)),
        ((nb072_alpha_dummy_136 A B R S_cls H), (nb072_alpha_dummy_137 y H)),
        ((nb072_alpha_dummy_132 A B R S_cls H), (nb072_alpha_dummy_134 y H)),
        ((nb072_alpha_dummy_133 A B R S_cls H), (nb072_alpha_dummy_135 y H)),
        ((nb072_alpha_dummy_158 A B R S_cls H), (nb072_alpha_dummy_159 y H)),
        ((nb072_alpha_dummy_156 A B R S_cls H), (nb072_alpha_dummy_157 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_154 A B R S_cls H), (nb072_alpha_dummy_155 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_132 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_139 A B R S_cls H) ≠ (nb072_alpha_dummy_150 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_150 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0146
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_151 y H) from (by
          unfold
            nb072_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0147
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_139 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0144
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_142 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0145
                    y H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_132
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_134 y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb072_alpha_dummy_140 A B R S_cls H) ≠ (nb072_alpha_dummy_152 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0150
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_153 y H) from (by
          unfold
            nb072_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0151
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_140 A B R S_cls H) ≠
        (nb072_alpha_dummy_148 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0148
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_143 y H) ≠ (nb072_alpha_dummy_149 y H) from (by
          unfold
            nb072_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0149
                    y H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_136;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0132 A B R S_cls H) 0)))) (show
                                (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from
                                (by
                                  unfold nb072_alpha_dummy_137;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0133 y H)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb072_alpha_dummy_136 A B R S_cls H),
                                (nb072_alpha_dummy_137 y H)),
                              ((nb072_alpha_dummy_132 A B R S_cls H),
                                (nb072_alpha_dummy_134 y H)),
                              ((nb072_alpha_dummy_133 A B R S_cls H),
                                (nb072_alpha_dummy_135 y H)),
                              ((nb072_alpha_dummy_158 A B R S_cls H),
                                (nb072_alpha_dummy_159 y H)),
                              ((nb072_alpha_dummy_156 A B R S_cls H),
                                (nb072_alpha_dummy_157 y H)),
                              ((nb072_alpha_dummy_125 A B R S_cls H),
                                (nb072_alpha_dummy_127 y H)),
                              ((nb072_alpha_dummy_124 A B R S_cls H),
                                (nb072_alpha_dummy_126 y H)),
                              ((nb072_alpha_dummy_154 A B R S_cls H),
                                (nb072_alpha_dummy_155 y H)),
                              ((nb072_alpha_dummy_128 A B R S_cls H),
                                (nb072_alpha_dummy_129 y H)),
                              ((nb072_alpha_dummy_116 A B R S_cls H),
                                (nb072_alpha_dummy_117 y H)),
                              ((nb072_alpha_dummy_118 A B R S_cls H),
                                (nb072_alpha_dummy_119 y H)),
                              ((nb072_alpha_dummy_121 A B R S_cls H),
                                (nb072_alpha_dummy_123 y H)),
                              ((nb072_alpha_dummy_120 A B R S_cls H),
                                (nb072_alpha_dummy_122 y H)),
                              ((nb072_alpha_dummy_039 A B R S_cls H),
                                (nb072_alpha_dummy_041 x y H)),
                              ((nb072_alpha_dummy_038 A B R S_cls H),
                                (nb072_alpha_dummy_040 x y H)),
                              ((nb072_alpha_dummy_114 A B R S_cls H),
                                (nb072_alpha_dummy_115 x y H)),
                              ((nb072_alpha_dummy_042 A B R S_cls H),
                                (nb072_alpha_dummy_043 x y H)),
                              ((nb072_alpha_dummy_001 A B R S_cls H), y),
                              ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                unfold nb072_alpha_dummy_136;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb072_support_mem_0132 A B R S_cls H) 0)))) (show
                              (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from (by
                                unfold nb072_alpha_dummy_137;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb072_support_mem_0133 y H) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb072_alpha_dummy_132 A B R S_cls H) ≠
                                  (nb072_alpha_dummy_136 A B R S_cls H) from (by
                                  unfold nb072_alpha_dummy_136;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb072_support_mem_0132 A B R S_cls H) 0)))) (show
                                (nb072_alpha_dummy_134 y H) ≠ (nb072_alpha_dummy_137 y H) from
                                (by
                                  unfold nb072_alpha_dummy_137;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb072_support_mem_0133 y H)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb072_alpha_dummy_136 A B R S_cls H),
                                (nb072_alpha_dummy_137 y H)),
                              ((nb072_alpha_dummy_132 A B R S_cls H),
                                (nb072_alpha_dummy_134 y H)),
                              ((nb072_alpha_dummy_133 A B R S_cls H),
                                (nb072_alpha_dummy_135 y H)),
                              ((nb072_alpha_dummy_158 A B R S_cls H),
                                (nb072_alpha_dummy_159 y H)),
                              ((nb072_alpha_dummy_156 A B R S_cls H),
                                (nb072_alpha_dummy_157 y H)),
                              ((nb072_alpha_dummy_125 A B R S_cls H),
                                (nb072_alpha_dummy_127 y H)),
                              ((nb072_alpha_dummy_124 A B R S_cls H),
                                (nb072_alpha_dummy_126 y H)),
                              ((nb072_alpha_dummy_154 A B R S_cls H),
                                (nb072_alpha_dummy_155 y H)),
                              ((nb072_alpha_dummy_128 A B R S_cls H),
                                (nb072_alpha_dummy_129 y H)),
                              ((nb072_alpha_dummy_116 A B R S_cls H),
                                (nb072_alpha_dummy_117 y H)),
                              ((nb072_alpha_dummy_118 A B R S_cls H),
                                (nb072_alpha_dummy_119 y H)),
                              ((nb072_alpha_dummy_121 A B R S_cls H),
                                (nb072_alpha_dummy_123 y H)),
                              ((nb072_alpha_dummy_120 A B R S_cls H),
                                (nb072_alpha_dummy_122 y H)),
                              ((nb072_alpha_dummy_039 A B R S_cls H),
                                (nb072_alpha_dummy_041 x y H)),
                              ((nb072_alpha_dummy_038 A B R S_cls H),
                                (nb072_alpha_dummy_040 x y H)),
                              ((nb072_alpha_dummy_114 A B R S_cls H),
                                (nb072_alpha_dummy_115 x y H)),
                              ((nb072_alpha_dummy_042 A B R S_cls H),
                                (nb072_alpha_dummy_043 x y H)),
                              ((nb072_alpha_dummy_001 A B R S_cls H), y),
                              ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C072C001Part015`. -/


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

theorem nb072_focused_notmem_0022 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_116 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar ((H).fv ∪ ((Class.cv (nb072_alpha_dummy_001 A B R S_cls H))).fv) 0 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb072_focused_notmem_0023 (y : Var) (H : Class) :
    (nb072_alpha_dummy_117 y H) ∉ H.fv :=
  by
  change freshVar ((H).fv ∪ ((Class.cv y)).fv) 0 ∉ H.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb072_focused_notmem_0024 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_118 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (({(nb072_alpha_dummy_116 A B R S_cls H)} : Finset Var) ∪
          ((syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
              (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
      (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0025 (y : Var) (H : Class) :
    (nb072_alpha_dummy_119 y H) ∉ H.fv :=
  by
  change
    freshVar
        (({(nb072_alpha_dummy_117 y H)} : Finset Var) ∪
          ((syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb072_focused_notmem_0026 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_121 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
                (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                  (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_118 A B R S_cls H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0024 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_116 A B R S_cls H)
        (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0022 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0027 (y : Var) (H : Class) :
    (nb072_alpha_dummy_123 y H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_117 y H)
                (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv)
        1 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_119 y H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H)
          (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_119 y H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0025 y H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_117 y H)
          (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_117 y H)
        (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0023 y H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0028 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_120 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
                (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                  (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_118 A B R S_cls H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0024 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
          (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_116 A B R S_cls H)
        (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_116 A B R S_cls H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0022 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
          (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0029 (y : Var) (H : Class) :
    (nb072_alpha_dummy_122 y H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_119 y H) (Wff.classEq
              (Class.cab (nb072_alpha_dummy_117 y H)
                (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
              (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_class_cab (nb072_alpha_dummy_119 y H)
      (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H)
          (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_119 y H))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0025 y H)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb072_alpha_dummy_117 y H)
          (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
        (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb072_alpha_dummy_117 y H)
        (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H)))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0023 y H)) (h_eq ▸ hu)
    · rw [fv_syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0030 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_114 A B R S_cls H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                    (syn_csn (syn_c0c))))))).fv ∪
          ((Class.cab (nb072_alpha_dummy_038 A B R S_cls H)
              (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
                (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
                    (syn_csn (syn_c0c))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb072_alpha_dummy_038 A B R S_cls H)
      (syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
        (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
          (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
            (syn_csn (syn_c0c)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0014 A B R S_cls H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072_alpha_dummy_039 A B R S_cls H)
        (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
          (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
            (syn_csn (syn_c0c))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0012 A B R S_cls H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H))]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_focused_notmem_0031 (x : Var) (y : Var) (H : Class) :
    (nb072_alpha_dummy_115 x y H) ∉ H.fv :=
  by
  change
    freshVar
        (((Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                    (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb072_alpha_dummy_040 x y H)
              (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
                (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
                  (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
                    (syn_csn (syn_c0c))))))).fv)
        0 ∉
      H.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb072_alpha_dummy_040 x y H)
      (syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
          (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb072_focused_notmem_0015 x y H)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb072_alpha_dummy_041 x y H) (syn_cfv H (Class.cv y))
        (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
          (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H))) (syn_csn (syn_c0c))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb072_focused_notmem_0013 x y H)) (h_eq ▸ hu)
    · rw [fv_syn_cfv H (Class.cv y)]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb072_compact_envfresh_0029 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) :
    TEnvFresh
      [((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      H.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072_alpha_dummy_116 A B R S_cls H) (nb072_alpha_dummy_117 y H)
      (nb072_focused_notmem_0022 A B R S_cls H) (nb072_focused_notmem_0023 y H)
      (TEnvFresh.consFresh (nb072_alpha_dummy_118 A B R S_cls H)
        (nb072_alpha_dummy_119 y H) (nb072_focused_notmem_0024 A B R S_cls H)
        (nb072_focused_notmem_0025 y H)
        (TEnvFresh.consFresh (nb072_alpha_dummy_121 A B R S_cls H)
          (nb072_alpha_dummy_123 y H) (nb072_focused_notmem_0026 A B R S_cls H)
          (nb072_focused_notmem_0027 y H)
          (TEnvFresh.consFresh (nb072_alpha_dummy_120 A B R S_cls H)
            (nb072_alpha_dummy_122 y H) (nb072_focused_notmem_0028 A B R S_cls H)
            (nb072_focused_notmem_0029 y H)
            (TEnvFresh.consFresh (nb072_alpha_dummy_039 A B R S_cls H)
              (nb072_alpha_dummy_041 x y H) (nb072_focused_notmem_0012 A B R S_cls H)
              (nb072_focused_notmem_0013 x y H)
              (TEnvFresh.consFresh (nb072_alpha_dummy_038 A B R S_cls H)
                (nb072_alpha_dummy_040 x y H) (nb072_focused_notmem_0014 A B R S_cls H)
                (nb072_focused_notmem_0015 x y H)
                (TEnvFresh.consFresh (nb072_alpha_dummy_114 A B R S_cls H)
                  (nb072_alpha_dummy_115 x y H) (nb072_focused_notmem_0030 A B R S_cls H)
                  (nb072_focused_notmem_0031 x y H)
                  (TEnvFresh.consFresh (nb072_alpha_dummy_042 A B R S_cls H)
                    (nb072_alpha_dummy_043 x y H) (nb072_focused_notmem_0018 A B R S_cls H)
                    (nb072_focused_notmem_0019 x y H)
                    (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y
                      (nb072_focused_notmem_0020 A B R S_cls H) dv_H_y
                      (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x
                        (nb072_focused_notmem_0021 A B R S_cls H) dv_H_x
                        (TEnvFresh.nil H.fv)))))))))))

@[expose]
noncomputable def nb072_focused_refl_0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) :
    TReflOn
      [((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      H.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0029 x y A B R S_cls H dv_H_x dv_H_y)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
