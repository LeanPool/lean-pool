/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part032`. -/


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
noncomputable def nb068_split_alpha_0068 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
        ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
        ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
        ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
        ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
        ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
        ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
        ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
        ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_145))
            (syn_cun (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_149 f))
            (Class.cv (nb068_alpha_dummy_150 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_148 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_149 f))
              (Class.cv (nb068_alpha_dummy_150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_153) from (by
                              unfold nb068_alpha_dummy_153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_154 f) from (by
                              unfold nb068_alpha_dummy_154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_151) from (by
                                unfold nb068_alpha_dummy_151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_152 f) from (by
                                unfold nb068_alpha_dummy_152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
          ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
          ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
          ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
          ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
          ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
          ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
          ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
          ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
          ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
          ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
          ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
          ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
          ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_157) from (by
                                unfold nb068_alpha_dummy_157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_158 f) from (by
                                unfold nb068_alpha_dummy_158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_157) from (by
                                unfold nb068_alpha_dummy_157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_158 f) from (by
                                unfold nb068_alpha_dummy_158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_159) from (by
                                unfold nb068_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_160 f) from (by
                                unfold nb068_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_159) from (by
                                unfold nb068_alpha_dummy_159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_160 f) from (by
                                unfold nb068_alpha_dummy_160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_147) ≠ (nb068_alpha_dummy_155) from (by
                                  unfold nb068_alpha_dummy_155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068_alpha_dummy_150 f) ≠ (nb068_alpha_dummy_156 f) from
                                (by
                                  unfold nb068_alpha_dummy_156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0069 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
        ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
        ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
        ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
        ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
        ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
        ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_139))
          (Class.cv (nb068_alpha_dummy_132))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_140))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_139)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_139)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_139))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f))
          (Class.cv (nb068_alpha_dummy_134 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_142 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_141 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_141 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_141 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_139) from (by
              unfold nb068_alpha_dummy_139;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 0))))
          (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_141 f) from (by
              unfold nb068_alpha_dummy_141;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_140) from (by
                unfold nb068_alpha_dummy_140;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0132) 1))))
            (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_142 f) from (by
                unfold nb068_alpha_dummy_142;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0133 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_165) from (by
                  unfold nb068_alpha_dummy_165;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0162) 0))))
              (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_166 f) from (by
                  unfold nb068_alpha_dummy_166;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0163 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_132) ≠ (nb068_alpha_dummy_163) from (by
                    unfold nb068_alpha_dummy_163;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0160) 0))))
                (show (nb068_alpha_dummy_134 f) ≠ (nb068_alpha_dummy_164 f) from (by
                    unfold nb068_alpha_dummy_164;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0161 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_132))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_134 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_146) from (by
                                  unfold nb068_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                              (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_149 f) from
                                (by
                                  unfold nb068_alpha_dummy_149;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_145) from (by
                                    unfold nb068_alpha_dummy_145;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0136) 0)))) (show
                                  (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_148 f) from (by
                                    unfold nb068_alpha_dummy_148;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0137 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from
                                    (by
                                      unfold nb068_alpha_dummy_143;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0134)
                                              0)))) (show
                                    (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from
                                    (by
                                      unfold nb068_alpha_dummy_144;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0135 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_147), (nb068_alpha_dummy_150 f)),
                                  ((nb068_alpha_dummy_146), (nb068_alpha_dummy_149 f)),
                                  ((nb068_alpha_dummy_145), (nb068_alpha_dummy_148 f)),
                                  ((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
                                  ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
                                  ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
                                  ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
                                  ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
                                  ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                                  ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                                  ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
                                  ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                                  ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                                  ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                                  ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                                  ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                                  ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0068 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                          unfold nb068_alpha_dummy_143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                          unfold nb068_alpha_dummy_144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
                      ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
                      ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
                      ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
                      ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
                      ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                      ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                      ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
                      ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                      ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                      ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                      ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                      ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                      ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from
                      (by
                        unfold nb068_alpha_dummy_143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                    (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                        unfold nb068_alpha_dummy_144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_143) from (by
                          unfold nb068_alpha_dummy_143;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                      (show (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_144 f) from (by
                          unfold nb068_alpha_dummy_144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_143), (nb068_alpha_dummy_144 f)),
                      ((nb068_alpha_dummy_139), (nb068_alpha_dummy_141 f)),
                      ((nb068_alpha_dummy_140), (nb068_alpha_dummy_142 f)),
                      ((nb068_alpha_dummy_165), (nb068_alpha_dummy_166 f)),
                      ((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
                      ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                      ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                      ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
                      ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                      ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                      ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                      ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                      ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                      ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0070 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
        ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_161))
          (Class.cab (nb068_alpha_dummy_131)
            (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_161))
            (Class.cab (nb068_alpha_dummy_131)
              (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_162 f))
          (Class.cab (nb068_alpha_dummy_133 f)
            (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_162 f))
            (Class.cab (nb068_alpha_dummy_133 f)
              (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_132) from
                    (by
                      unfold nb068_alpha_dummy_132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                  (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_134 f) from (by
                      unfold nb068_alpha_dummy_134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_131) from
                      (by
                        unfold nb068_alpha_dummy_131;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                    (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_133 f) from (by
                        unfold nb068_alpha_dummy_133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_161) from (by
                          unfold nb068_alpha_dummy_161;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_162 f) from (by
                          unfold nb068_alpha_dummy_162;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_135) from (by
                            unfold nb068_alpha_dummy_135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                        (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_136 f) from (by
                            unfold nb068_alpha_dummy_136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0069 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0069 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
                          ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                          ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                          ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
                          ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                          ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                          ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_132) from
                      (by
                        unfold nb068_alpha_dummy_132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                    (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_134 f) from (by
                        unfold nb068_alpha_dummy_134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_131) from (by
                          unfold nb068_alpha_dummy_131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                      (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_133 f) from (by
                          unfold nb068_alpha_dummy_133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_161) from (by
                            unfold nb068_alpha_dummy_161;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                        (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_162 f) from (by
                            unfold nb068_alpha_dummy_162;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_135) from (by
                              unfold nb068_alpha_dummy_135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                          (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_136 f) from (by
                              unfold nb068_alpha_dummy_136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0069 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0069 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_163), (nb068_alpha_dummy_164 f)),
                            ((nb068_alpha_dummy_132), (nb068_alpha_dummy_134 f)),
                            ((nb068_alpha_dummy_131), (nb068_alpha_dummy_133 f)),
                            ((nb068_alpha_dummy_161), (nb068_alpha_dummy_162 f)),
                            ((nb068_alpha_dummy_135), (nb068_alpha_dummy_136 f)),
                            ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                            ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                            ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                            ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                            ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0071 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
        ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
        ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
        ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
        ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_181))
            (syn_cun (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_184 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_185 f))
              (Class.cv (nb068_alpha_dummy_186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
          ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
          ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
          ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
          ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
          ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
          ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
          ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
          ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0072 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_175))
            (Class.cv (nb068_alpha_dummy_168))) (Wff.classEq (Class.cv (nb068_alpha_dummy_176))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_175))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f))
            (Class.cv (nb068_alpha_dummy_170 f)))
          (Wff.classEq (Class.cv (nb068_alpha_dummy_178 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_177 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from (by
                unfold nb068_alpha_dummy_175;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0))))
            (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_177 f) from (by
                unfold nb068_alpha_dummy_177;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0))))
            (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from (by
                  unfold nb068_alpha_dummy_176;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1))))
              (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_178 f) from (by
                  unfold nb068_alpha_dummy_178;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1))))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_182) from (by
                                  unfold nb068_alpha_dummy_182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_185 f) from
                                (by
                                  unfold nb068_alpha_dummy_185;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_181) from (by
                                    unfold nb068_alpha_dummy_181;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0174) 0)))) (show
                                  (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_184 f) from (by
                                    unfold nb068_alpha_dummy_184;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0175 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from
                                    (by
                                      unfold nb068_alpha_dummy_179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0172)
                                              0)))) (show
                                    (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from
                                    (by
                                      unfold nb068_alpha_dummy_180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0173 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
                                  ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
                                  ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
                                  ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                                  ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                                  ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                                  ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                                  ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                                  ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
                                  ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                                  ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                                  ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                                  ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                                  ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                                  ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0071 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                          unfold nb068_alpha_dummy_179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                          unfold nb068_alpha_dummy_180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                      ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                      ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                      ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                      ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                      ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
                      ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                      ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                      ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                      ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                      ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                      ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from
                      (by
                        unfold nb068_alpha_dummy_179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                    (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                        unfold nb068_alpha_dummy_180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                          unfold nb068_alpha_dummy_179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                          unfold nb068_alpha_dummy_180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                      ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                      ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                      ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                      ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                      ((nb068_alpha_dummy_173), (nb068_alpha_dummy_174 f)),
                      ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                      ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                      ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                      ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                      ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                      ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part033`. -/


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
noncomputable def nb068_split_alpha_0073 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
        ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
        ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
        ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
        ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
        ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_181))
            (syn_cun (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_185 f))
            (Class.cv (nb068_alpha_dummy_186 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_184 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_185 f))
              (Class.cv (nb068_alpha_dummy_186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_189) from (by
                              unfold nb068_alpha_dummy_189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_190 f) from (by
                              unfold nb068_alpha_dummy_190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_187) from (by
                                unfold nb068_alpha_dummy_187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_188 f) from (by
                                unfold nb068_alpha_dummy_188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
          ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
          ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
          ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
          ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
          ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
          ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
          ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
          ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
          ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
          ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_193) from (by
                                unfold nb068_alpha_dummy_193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_194 f) from (by
                                unfold nb068_alpha_dummy_194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_182) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068_alpha_dummy_185 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_195) from (by
                                unfold nb068_alpha_dummy_195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_196 f) from (by
                                unfold nb068_alpha_dummy_196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_183) ≠ (nb068_alpha_dummy_191) from (by
                                  unfold nb068_alpha_dummy_191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068_alpha_dummy_186 f) ≠ (nb068_alpha_dummy_192 f) from
                                (by
                                  unfold nb068_alpha_dummy_192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0074 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
        ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
        ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
        ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
        ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
        ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
        ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_175))
          (Class.cv (nb068_alpha_dummy_168))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_176))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_175)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_175)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_175))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f))
          (Class.cv (nb068_alpha_dummy_170 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_178 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_177 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_177 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_177 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_175) from (by
              unfold nb068_alpha_dummy_175;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 0))))
          (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_177 f) from (by
              unfold nb068_alpha_dummy_177;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_176) from (by
                unfold nb068_alpha_dummy_176;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0170) 1))))
            (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_178 f) from (by
                unfold nb068_alpha_dummy_178;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0171 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_201) from (by
                  unfold nb068_alpha_dummy_201;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0200) 0))))
              (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_202 f) from (by
                  unfold nb068_alpha_dummy_202;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0201 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_168) ≠ (nb068_alpha_dummy_199) from (by
                    unfold nb068_alpha_dummy_199;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0198) 0))))
                (show (nb068_alpha_dummy_170 f) ≠ (nb068_alpha_dummy_200 f) from (by
                    unfold nb068_alpha_dummy_200;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0199 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_168))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_170 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_182) from (by
                                  unfold nb068_alpha_dummy_182;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                              (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_185 f) from
                                (by
                                  unfold nb068_alpha_dummy_185;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_181) from (by
                                    unfold nb068_alpha_dummy_181;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0174) 0)))) (show
                                  (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_184 f) from (by
                                    unfold nb068_alpha_dummy_184;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0175 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from
                                    (by
                                      unfold nb068_alpha_dummy_179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0172)
                                              0)))) (show
                                    (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from
                                    (by
                                      unfold nb068_alpha_dummy_180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0173 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_183), (nb068_alpha_dummy_186 f)),
                                  ((nb068_alpha_dummy_182), (nb068_alpha_dummy_185 f)),
                                  ((nb068_alpha_dummy_181), (nb068_alpha_dummy_184 f)),
                                  ((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                                  ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                                  ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                                  ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
                                  ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                                  ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                                  ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                                  ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                                  ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                                  ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                                  ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                                  ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                                  ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                                  ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0073 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                          unfold nb068_alpha_dummy_179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                          unfold nb068_alpha_dummy_180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                      ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                      ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                      ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
                      ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                      ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                      ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                      ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                      ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                      ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                      ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                      ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                      ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                      ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from
                      (by
                        unfold nb068_alpha_dummy_179;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                    (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                        unfold nb068_alpha_dummy_180;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_175) ≠ (nb068_alpha_dummy_179) from (by
                          unfold nb068_alpha_dummy_179;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                      (show (nb068_alpha_dummy_177 f) ≠ (nb068_alpha_dummy_180 f) from (by
                          unfold nb068_alpha_dummy_180;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_179), (nb068_alpha_dummy_180 f)),
                      ((nb068_alpha_dummy_175), (nb068_alpha_dummy_177 f)),
                      ((nb068_alpha_dummy_176), (nb068_alpha_dummy_178 f)),
                      ((nb068_alpha_dummy_201), (nb068_alpha_dummy_202 f)),
                      ((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                      ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                      ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                      ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                      ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                      ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                      ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                      ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                      ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                      ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0075 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
        ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
        ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_197))
          (Class.cab (nb068_alpha_dummy_167)
            (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_197))
            (Class.cab (nb068_alpha_dummy_167)
              (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_198 f))
          (Class.cab (nb068_alpha_dummy_169 f)
            (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_198 f))
            (Class.cab (nb068_alpha_dummy_169 f)
              (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_168) from
                    (by
                      unfold nb068_alpha_dummy_168;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                  (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_170 f) from (by
                      unfold nb068_alpha_dummy_170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_167) from
                      (by
                        unfold nb068_alpha_dummy_167;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                    (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_169 f) from (by
                        unfold nb068_alpha_dummy_169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_197) from (by
                          unfold nb068_alpha_dummy_197;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                      (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_198 f) from (by
                          unfold nb068_alpha_dummy_198;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_171) from (by
                            unfold nb068_alpha_dummy_171;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                        (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_172 f) from (by
                            unfold nb068_alpha_dummy_172;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0074 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0074 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                          ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                          ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                          ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                          ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                          ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                          ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                          ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                          ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                          ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_168) from
                      (by
                        unfold nb068_alpha_dummy_168;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
                    (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_170 f) from (by
                        unfold nb068_alpha_dummy_170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0194 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_167) from (by
                          unfold nb068_alpha_dummy_167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0192) 0))))
                      (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_169 f) from (by
                          unfold nb068_alpha_dummy_169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_197) from (by
                            unfold nb068_alpha_dummy_197;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                        (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_198 f) from (by
                            unfold nb068_alpha_dummy_198;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_171) from (by
                              unfold nb068_alpha_dummy_171;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                          (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_172 f) from (by
                              unfold nb068_alpha_dummy_172;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0074 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0074 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_199), (nb068_alpha_dummy_200 f)),
                            ((nb068_alpha_dummy_168), (nb068_alpha_dummy_170 f)),
                            ((nb068_alpha_dummy_167), (nb068_alpha_dummy_169 f)),
                            ((nb068_alpha_dummy_197), (nb068_alpha_dummy_198 f)),
                            ((nb068_alpha_dummy_171), (nb068_alpha_dummy_172 f)),
                            ((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
                            ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
                            ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
                            ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                            ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0076 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_126), (nb068_alpha_dummy_128 f)),
        ((nb068_alpha_dummy_125), (nb068_alpha_dummy_127 f)),
        ((nb068_alpha_dummy_129), (nb068_alpha_dummy_130 f)),
        ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
        ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb068_alpha_dummy_129))
          (syn_cop (Class.cv (nb068_alpha_dummy_125)) (Class.cv (nb068_alpha_dummy_126))))
        (Wff.neg (syn_wbr (Class.cv (nb068_alpha_dummy_126)) (Class.cv (nb068_alpha_dummy_000))
            (Class.cv (nb068_alpha_dummy_125)))))
      (Wff.imp (Wff.classEq (Class.cv (nb068_alpha_dummy_130 f))
          (syn_cop (Class.cv (nb068_alpha_dummy_127 f)) (Class.cv (nb068_alpha_dummy_128 f))))
        (Wff.neg (syn_wbr (Class.cv (nb068_alpha_dummy_128 f)) (Class.cv f)
            (Class.cv (nb068_alpha_dummy_127 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_129) from (by
                unfold nb068_alpha_dummy_129;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0))))) (Ne.symm
            (show (nb068_alpha_dummy_128 f) ≠ (nb068_alpha_dummy_130 f) from (by
                unfold nb068_alpha_dummy_130;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_129) from
                (by
                  unfold nb068_alpha_dummy_129;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
            (Ne.symm (show (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_130 f) from (by
                  unfold nb068_alpha_dummy_130;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from
                                    (by
                                      unfold nb068_alpha_dummy_132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_134 f) from
                                    (by
                                      unfold nb068_alpha_dummy_134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_131) from (by
                                        unfold nb068_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068_alpha_dummy_127 f) ≠
                                        (nb068_alpha_dummy_133 f) from (by
                                        unfold nb068_alpha_dummy_133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_137) from
                                        (by
                                          unfold nb068_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_138 f) from (by
                                          unfold nb068_alpha_dummy_138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠
        (nb068_alpha_dummy_135) from (by
          unfold nb068_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_136 f) from (by
          unfold nb068_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb068_split_alpha_0067 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_132) from
                                    (by
                                      unfold nb068_alpha_dummy_132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0126)
                                              1)))) (show
                                    (nb068_alpha_dummy_127 f) ≠ (nb068_alpha_dummy_134 f) from
                                    (by
                                      unfold nb068_alpha_dummy_134;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0128 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_131) from (by
                                        unfold nb068_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0126)
                                                0)))) (show (nb068_alpha_dummy_127 f) ≠
                                        (nb068_alpha_dummy_133 f) from (by
                                        unfold nb068_alpha_dummy_133;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0128 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_137) from
                                        (by
                                          unfold nb068_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0130)
                                                  0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_138 f) from (by
                                          unfold nb068_alpha_dummy_138;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0131 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_125) ≠
        (nb068_alpha_dummy_135) from (by
          unfold nb068_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068_alpha_dummy_127 f) ≠
        (nb068_alpha_dummy_136 f) from (by
          unfold nb068_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068_alpha_dummy_125))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_126))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪
                                      ((Class.cv (nb068_alpha_dummy_128 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.all (nb068_split_alpha_0067 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0070 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
                                        unfold nb068_alpha_dummy_168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068_alpha_dummy_128 f) ≠
                                        (nb068_alpha_dummy_170 f) from (by
                                        unfold nb068_alpha_dummy_170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from
                                        (by
                                          unfold nb068_alpha_dummy_167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_169 f) from (by
                                          unfold nb068_alpha_dummy_169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠
        (nb068_alpha_dummy_173) from (by
          unfold nb068_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_174 f) from (by
          unfold nb068_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_171) from (by
          unfold nb068_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_172 f) from (by
          unfold nb068_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb068_split_alpha_0072 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_168) from (by
                                        unfold nb068_alpha_dummy_168;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0164)
                                                1)))) (show (nb068_alpha_dummy_128 f) ≠
                                        (nb068_alpha_dummy_170 f) from (by
                                        unfold nb068_alpha_dummy_170;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0166 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_167) from
                                        (by
                                          unfold nb068_alpha_dummy_167;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0164)
                                                  0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_169 f) from (by
                                          unfold nb068_alpha_dummy_169;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0166 f) 0))))
                                      (TAlphaVar.there (show (nb068_alpha_dummy_126) ≠
        (nb068_alpha_dummy_173) from (by
          unfold nb068_alpha_dummy_173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0168) 0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_174 f) from (by
          unfold nb068_alpha_dummy_174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_126) ≠ (nb068_alpha_dummy_171) from (by
          unfold nb068_alpha_dummy_171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0165) 0)))) (show (nb068_alpha_dummy_128 f) ≠
        (nb068_alpha_dummy_172 f) from (by
          unfold nb068_alpha_dummy_172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0167 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_126))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_125))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪
                                        ((Class.cv (nb068_alpha_dummy_127 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.all (nb068_split_alpha_0072 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0075 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_126) from (by
                unfold nb068_alpha_dummy_126;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1))))
            (show f ≠ (nb068_alpha_dummy_128 f) from (by
                unfold nb068_alpha_dummy_128;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_125) from (by
                  unfold nb068_alpha_dummy_125;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0))))
              (show f ≠ (nb068_alpha_dummy_127 f) from (by
                  unfold nb068_alpha_dummy_127;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_129) from (by
                    unfold nb068_alpha_dummy_129;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0210) 0))))
                (show f ≠ (nb068_alpha_dummy_130 f) from (by
                    unfold nb068_alpha_dummy_130;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_240) from
                    (by
                      unfold nb068_alpha_dummy_240;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0290) 1))))
                  (show f ≠ (nb068_alpha_dummy_242 f) from (by
                      unfold nb068_alpha_dummy_242;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0291 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_239) from
                      (by
                        unfold nb068_alpha_dummy_239;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0290) 0))))
                    (show f ≠ (nb068_alpha_dummy_241 f) from (by
                        unfold nb068_alpha_dummy_241;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0291 f) 0))))
                    (TAlphaVar.here _ _ _))))))))))

@[expose]
noncomputable def nb068_split_alpha_0077 (x : Var) (y : Var) (f : Var) (dv_f_x : f ≠ x)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (syn_wfun (Class.cv (nb068_alpha_dummy_000))) (Wff.neg
          (Wff.classEq (syn_cdm (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_001)))))
      (Wff.imp (syn_wfun (Class.cv f))
        (Wff.neg (Wff.classEq (syn_cdm (Class.cv f)) (Class.cv x)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0033 x y f))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                      (show (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_051) from (by
                          unfold nb068_alpha_dummy_051;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0044) 0))))) (Ne.symm
                      (show (nb068_alpha_dummy_049 f) ≠ (nb068_alpha_dummy_052 f) from (by
                          unfold nb068_alpha_dummy_052;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0045 f) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_051) from (by
                            unfold nb068_alpha_dummy_051;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0042) 0))))) (Ne.symm
                        (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_052 f) from (by
                            unfold nb068_alpha_dummy_052;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0043 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
          unfold nb068_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 1)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_056 f) from (by
          unfold nb068_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053) from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_059) from (by
          unfold nb068_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050) 0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_060 f) from (by
          unfold nb068_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_057)
        from (by
          unfold nb068_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_058 f) from (by
          unfold nb068_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb068_split_alpha_0035 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_054) from (by
          unfold nb068_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 1)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_056 f) from (by
          unfold nb068_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_053) from (by
          unfold nb068_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0046) 0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_055 f) from (by
          unfold nb068_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0048 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_059) from (by
          unfold nb068_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0050) 0)))) (show (nb068_alpha_dummy_048 f) ≠
        (nb068_alpha_dummy_060 f) from (by
          unfold nb068_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0051 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_057)
        from (by
          unfold nb068_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0047)
                  0)))) (show (nb068_alpha_dummy_048 f) ≠ (nb068_alpha_dummy_058 f) from (by
          unfold nb068_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0049 f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb068_split_alpha_0035 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb068_split_alpha_0038 x y f)))))))))
              (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0060 x y f)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)),
                    ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)),
                    ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                    ((nb068_alpha_dummy_001), x),
                    ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_244) from (by
          unfold nb068_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 1)))) (show (nb068_alpha_dummy_242 f) ≠
        (nb068_alpha_dummy_246 f) from (by
          unfold nb068_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_243) from (by
          unfold nb068_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 0)))) (show (nb068_alpha_dummy_242 f) ≠
        (nb068_alpha_dummy_245 f) from (by
          unfold nb068_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_249) from (by
          unfold nb068_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0256) 0)))) (show (nb068_alpha_dummy_242 f) ≠
        (nb068_alpha_dummy_250 f) from (by
          unfold nb068_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0257 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_247)
        from (by
          unfold nb068_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0253)
                  0)))) (show (nb068_alpha_dummy_242 f) ≠ (nb068_alpha_dummy_248 f) from (by
          unfold nb068_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0255 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0062 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_244) from (by
          unfold nb068_alpha_dummy_244;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 1)))) (show (nb068_alpha_dummy_242 f) ≠
        (nb068_alpha_dummy_246 f) from (by
          unfold nb068_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 1)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_243) from (by
          unfold nb068_alpha_dummy_243;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0252) 0)))) (show (nb068_alpha_dummy_242 f) ≠
        (nb068_alpha_dummy_245 f) from (by
          unfold nb068_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0254 f) 0)))) (TAlphaVar.there (show
        (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_249) from (by
          unfold nb068_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0256) 0)))) (show (nb068_alpha_dummy_242 f) ≠
        (nb068_alpha_dummy_250 f) from (by
          unfold nb068_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0257 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_240) ≠ (nb068_alpha_dummy_247)
        from (by
          unfold nb068_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0253)
                  0)))) (show (nb068_alpha_dummy_242 f) ≠ (nb068_alpha_dummy_248 f) from (by
          unfold nb068_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0255 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0062 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb068_split_alpha_0065 x y f))))))))
                (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.ex (TAlphaWff.neg (nb068_split_alpha_0076 x y f)))))))))
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_f_x)
            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
              (TAlphaVar.here _ _ _)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part034`. -/


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
noncomputable def nb068_split_alpha_0078 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
        ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
        ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
        ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
        ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
        ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
        ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
        ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_301))
            (syn_cun (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_304 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_305 f))
              (Class.cv (nb068_alpha_dummy_306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
          ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
          ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
          ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
          ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
          ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
          ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0079 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
        ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
        (syn_cphi (Class.cv (nb068_alpha_dummy_288))))
      (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
        (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
            ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_295) from (by
                    unfold nb068_alpha_dummy_295;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
                (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_297 f) from (by
                    unfold nb068_alpha_dummy_297;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
                (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_296) from
                    (by
                      unfold nb068_alpha_dummy_296;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
                  (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_298 f) from (by
                      unfold nb068_alpha_dummy_298;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_302) from
                                    (by
                                      unfold nb068_alpha_dummy_302;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0302)
                                              1)))) (show
                                    (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_305 f) from
                                    (by
                                      unfold nb068_alpha_dummy_305;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0303 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_301) from (by
                                        unfold nb068_alpha_dummy_301;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0302)
                                                0)))) (show (nb068_alpha_dummy_297 f) ≠
                                        (nb068_alpha_dummy_304 f) from (by
                                        unfold nb068_alpha_dummy_304;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0303 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from
                                        (by
                                          unfold nb068_alpha_dummy_299;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0300)
                                                  0)))) (show (nb068_alpha_dummy_297 f) ≠
        (nb068_alpha_dummy_300 f) from (by
                                          unfold nb068_alpha_dummy_300;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0301 f) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
                                      ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
                                      ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
                                      ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                                      ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                                      ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                                      ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                                      ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                                      ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
                                      ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                                      ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                                      ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                                      ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                                      ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                                      ((nb068_alpha_dummy_000), f),
                                      ((nb068_alpha_dummy_002), y),
                                      ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                        (nb068_alpha_dummy_004 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb068_split_alpha_0078 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                              unfold nb068_alpha_dummy_299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                              unfold nb068_alpha_dummy_300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                          ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
                          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                          ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                          ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                            unfold nb068_alpha_dummy_299;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                        (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                            unfold nb068_alpha_dummy_300;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                              unfold nb068_alpha_dummy_299;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                          (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                              unfold nb068_alpha_dummy_300;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                          ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
                          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                          ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                          ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part035`. -/


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
noncomputable def nb068_split_alpha_0080 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
        ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
        ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
        ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
        ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
        ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
        ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
        ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
        ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
        ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_301))
            (syn_cun (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_304 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_305 f))
              (Class.cv (nb068_alpha_dummy_306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
          ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
          ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
          ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
          ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
          ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
          ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
          ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
          ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0081 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
        ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
        ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
        ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
        ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
        ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_295))
          (Class.cv (nb068_alpha_dummy_288))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_296))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_295))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_297 f))
          (Class.cv (nb068_alpha_dummy_290 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_298 f))
            (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))
              (Class.cv (nb068_alpha_dummy_297 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_295) from (by
              unfold nb068_alpha_dummy_295;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0))))
          (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_297 f) from (by
              unfold nb068_alpha_dummy_297;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0))))
          (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_296) from (by
                unfold nb068_alpha_dummy_296;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1))))
            (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_298 f) from (by
                unfold nb068_alpha_dummy_298;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1))))
            (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_321) from (by
                  unfold nb068_alpha_dummy_321;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0328) 0))))
              (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_322 f) from (by
                  unfold nb068_alpha_dummy_322;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0329 f) 0))))
              (TAlphaVar.there (show (nb068_alpha_dummy_288) ≠ (nb068_alpha_dummy_319) from (by
                    unfold nb068_alpha_dummy_319;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0326) 0))))
                (show (nb068_alpha_dummy_290 f) ≠ (nb068_alpha_dummy_320 f) from (by
                    unfold nb068_alpha_dummy_320;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0327 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_302) from (by
                                  unfold nb068_alpha_dummy_302;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0302) 1))))
                              (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_305 f) from
                                (by
                                  unfold nb068_alpha_dummy_305;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0303 f) 1))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_301) from (by
                                    unfold nb068_alpha_dummy_301;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0302) 0)))) (show
                                  (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_304 f) from (by
                                    unfold nb068_alpha_dummy_304;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0303 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from
                                    (by
                                      unfold nb068_alpha_dummy_299;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0300)
                                              0)))) (show
                                    (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from
                                    (by
                                      unfold nb068_alpha_dummy_300;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0301 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
                                  ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
                                  ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
                                  ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                                  ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                                  ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                                  ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
                                  ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                                  ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                                  ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                                  ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                                  ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                                  ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                                  ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                                  ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                                  ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                                  ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                                  ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003),
                                    (nb068_alpha_dummy_004 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068_split_alpha_0080 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                          unfold nb068_alpha_dummy_299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                          unfold nb068_alpha_dummy_300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                      ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                      ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                      ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
                      ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                      ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                      ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                      ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                      ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                      ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                      ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                      ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                      ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from
                      (by
                        unfold nb068_alpha_dummy_299;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                    (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                        unfold nb068_alpha_dummy_300;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_295) ≠ (nb068_alpha_dummy_299) from (by
                          unfold nb068_alpha_dummy_299;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0300) 0))))
                      (show (nb068_alpha_dummy_297 f) ≠ (nb068_alpha_dummy_300 f) from (by
                          unfold nb068_alpha_dummy_300;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0301 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
                      ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
                      ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
                      ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)),
                      ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                      ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                      ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                      ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                      ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                      ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                      ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                      ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                      ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                      ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                      ((nb068_alpha_dummy_001), x),
                      ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb068_split_alpha_0082 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
        ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_317))
          (Class.cab (nb068_alpha_dummy_287)
            (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_317))
            (Class.cab (nb068_alpha_dummy_287)
              (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_287))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_318 f))
          (Class.cab (nb068_alpha_dummy_289 f)
            (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
              (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_318 f))
            (Class.cab (nb068_alpha_dummy_289 f)
              (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f))
                (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f))
                  (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_288) from
                    (by
                      unfold nb068_alpha_dummy_288;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                  (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_290 f) from (by
                      unfold nb068_alpha_dummy_290;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
                  (TAlphaVar.there (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_287) from
                      (by
                        unfold nb068_alpha_dummy_287;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                    (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_289 f) from (by
                        unfold nb068_alpha_dummy_289;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 0)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_317) from (by
                          unfold nb068_alpha_dummy_317;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                      (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_318 f) from (by
                          unfold nb068_alpha_dummy_318;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_291) from (by
                            unfold nb068_alpha_dummy_291;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                        (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_292 f) from (by
                            unfold nb068_alpha_dummy_292;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_284))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_283))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
                      ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0081 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068_split_alpha_0081 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                          ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                          ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                          ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_288) from
                      (by
                        unfold nb068_alpha_dummy_288;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
                    (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_290 f) from (by
                        unfold nb068_alpha_dummy_290;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0322 f) 1)))) (TAlphaVar.there
                      (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_287) from (by
                          unfold nb068_alpha_dummy_287;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0320) 0))))
                      (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_289 f) from (by
                          unfold nb068_alpha_dummy_289;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
                      (TAlphaVar.there
                        (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_317) from (by
                            unfold nb068_alpha_dummy_317;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0324) 0))))
                        (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_318 f) from (by
                            unfold nb068_alpha_dummy_318;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0325 f) 0))))
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_291) from (by
                              unfold nb068_alpha_dummy_291;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0321) 0))))
                          (show (nb068_alpha_dummy_285 f) ≠ (nb068_alpha_dummy_292 f) from (by
                              unfold nb068_alpha_dummy_292;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0323 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv)
                              (by decide))
                            (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068_alpha_dummy_284))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_283))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪
                        ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0081 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068_split_alpha_0081 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)),
                            ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
                            ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
                            ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)),
                            ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
                            ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                            ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                            ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                            ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0083 (x : Var) (y : Var) (f : Var) (dv_f_y : f ≠ y) :
    TAlphaWff
      [((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_279))
          (syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
            (Class.cv (nb068_alpha_dummy_002)))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_279))
            (syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000)))
              (Class.cv (nb068_alpha_dummy_002))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_280 y f))
          (syn_cnin (syn_crn (Class.cv f)) (Class.cv y))) (Wff.neg
          (Wff.classMem (Class.cv (nb068_alpha_dummy_280 y f))
            (syn_cnin (syn_crn (Class.cv f)) (Class.cv y))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                          ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                          ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                          ((nb068_alpha_dummy_001), x),
                          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                        (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_288) from (by
          unfold nb068_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
          unfold nb068_alpha_dummy_290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287)
        from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_293)
        from (by
          unfold nb068_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_294 f) from (by
          unfold nb068_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_291)
        from (by
          unfold nb068_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_292 f) from (by
          unfold nb068_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0079 x y f)))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_288) from (by
          unfold nb068_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
          unfold nb068_alpha_dummy_290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287)
        from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_293)
        from (by
          unfold nb068_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_294 f) from (by
          unfold nb068_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_291)
        from (by
          unfold nb068_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_292 f) from (by
          unfold nb068_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0079 x y f)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb068_split_alpha_0082 x y f))))))))
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_284) from (by
                              unfold nb068_alpha_dummy_284;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0334) 1))))
                          (show f ≠ (nb068_alpha_dummy_286 f) from (by
                              unfold nb068_alpha_dummy_286;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0335 f) 1))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_283) from (by
                                unfold nb068_alpha_dummy_283;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0334) 0))))
                            (show f ≠ (nb068_alpha_dummy_285 f) from (by
                                unfold nb068_alpha_dummy_285;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0335 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_281) from (by
                                  unfold nb068_alpha_dummy_281;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0332) 0))))
                              (show f ≠ (nb068_alpha_dummy_282 y f) from (by
                                  unfold nb068_alpha_dummy_282;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0333 y f)
                                          0)))) (TAlphaVar.there
                                (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_279) from (by
                                    unfold nb068_alpha_dummy_279;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0330) 0))))
                                (show f ≠ (nb068_alpha_dummy_280 y f) from (by
                                    unfold nb068_alpha_dummy_280;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0331 y f)
                                            0)))) (TAlphaVar.here _ _ _)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_281) from
                    (by
                      unfold nb068_alpha_dummy_281;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0338) 0))))
                  (show y ≠ (nb068_alpha_dummy_282 y f) from (by
                      unfold nb068_alpha_dummy_282;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb068_support_mem_0339 y f) 0)))) (TAlphaVar.there
                    (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_279) from (by
                        unfold nb068_alpha_dummy_279;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0336) 0))))
                    (show y ≠ (nb068_alpha_dummy_280 y f) from (by
                        unfold nb068_alpha_dummy_280;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0337 y f) 0))))
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                      (Ne.symm dv_f_y) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
                            ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
                            ((nb068_alpha_dummy_281), (nb068_alpha_dummy_282 y f)),
                            ((nb068_alpha_dummy_279), (nb068_alpha_dummy_280 y f)),
                            ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
                            ((nb068_alpha_dummy_001), x),
                            ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
                          (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_288) from (by
          unfold nb068_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
          unfold nb068_alpha_dummy_290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287)
        from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_293)
        from (by
          unfold nb068_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_294 f) from (by
          unfold nb068_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_291)
        from (by
          unfold
            nb068_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_292 f) from (by
          unfold
            nb068_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0079 x y f)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_288) from (by
          unfold nb068_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  1)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_290 f) from (by
          unfold nb068_alpha_dummy_290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294 f)
                  1)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_287)
        from (by
          unfold nb068_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0292)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_289 f) from (by
          unfold nb068_alpha_dummy_289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0294
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_293)
        from (by
          unfold nb068_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0296)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_294 f) from (by
          unfold nb068_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0297
                    f)
                  0)))) (TAlphaVar.there (show (nb068_alpha_dummy_284) ≠ (nb068_alpha_dummy_291)
        from (by
          unfold
            nb068_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0293)
                  0)))) (show (nb068_alpha_dummy_286 f) ≠ (nb068_alpha_dummy_292 f) from (by
          unfold
            nb068_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0295
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068_split_alpha_0079 x y f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb068_split_alpha_0082 x y f))))))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_284) from (by
                                unfold nb068_alpha_dummy_284;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0334) 1))))
                            (show f ≠ (nb068_alpha_dummy_286 f) from (by
                                unfold nb068_alpha_dummy_286;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0335 f) 1))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_283) from (by
                                  unfold nb068_alpha_dummy_283;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0334) 0))))
                              (show f ≠ (nb068_alpha_dummy_285 f) from (by
                                  unfold nb068_alpha_dummy_285;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0335 f) 0))))
                              (TAlphaVar.there
                                (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_281) from (by
                                    unfold nb068_alpha_dummy_281;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0332) 0))))
                                (show f ≠ (nb068_alpha_dummy_282 y f) from (by
                                    unfold nb068_alpha_dummy_282;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0333 y f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068_alpha_dummy_000) ≠ (nb068_alpha_dummy_279) from
                                    (by
                                      unfold nb068_alpha_dummy_279;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0330)
                                              0)))) (show f ≠ (nb068_alpha_dummy_280 y f) from
                                    (by
                                      unfold nb068_alpha_dummy_280;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0331 y f)
                                              0)))) (TAlphaVar.here _ _ _)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_281) from
                      (by
                        unfold nb068_alpha_dummy_281;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0338) 0))))
                    (show y ≠ (nb068_alpha_dummy_282 y f) from (by
                        unfold nb068_alpha_dummy_282;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0339 y f) 0))))
                    (TAlphaVar.there
                      (show (nb068_alpha_dummy_002) ≠ (nb068_alpha_dummy_279) from (by
                          unfold nb068_alpha_dummy_279;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0336) 0))))
                      (show y ≠ (nb068_alpha_dummy_280 y f) from (by
                          unfold nb068_alpha_dummy_280;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0337 y f) 0))))
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        (Ne.symm dv_f_y) (TAlphaVar.here _ _ _))))))))))))

@[expose]
noncomputable def nb068_split_alpha_0084 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
        ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
        ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
        ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
        ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
        ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
        ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
        ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
        ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
        ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
        ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
        ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
        ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
        ((nb068_alpha_dummy_001), x),
        ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_301))
            (syn_cun (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_305 f))
            (Class.cv (nb068_alpha_dummy_306 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068_alpha_dummy_304 f))
            (syn_cun (Class.cv (nb068_alpha_dummy_305 f))
              (Class.cv (nb068_alpha_dummy_306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0306) 0))))
                          (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0307 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0304) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0305 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_309) from (by
                              unfold nb068_alpha_dummy_309;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0310) 0))))
                          (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_310 f) from (by
                              unfold nb068_alpha_dummy_310;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0311 f) 0))))
                          (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_307) from (by
                                unfold nb068_alpha_dummy_307;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0308) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_308 f) from (by
                                unfold nb068_alpha_dummy_308;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0309 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)),
          ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)),
          ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)),
          ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)),
          ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)),
          ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)),
          ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)),
          ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)),
          ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)),
          ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)),
          ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)),
          ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)),
          ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y),
          ((nb068_alpha_dummy_001), x),
          ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_313) from (by
                                unfold nb068_alpha_dummy_313;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0314) 0))))
                            (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_314 f) from (by
                                unfold nb068_alpha_dummy_314;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0315 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_302) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0312) 0))))
                              (show (nb068_alpha_dummy_305 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0313 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_315) from (by
                                unfold nb068_alpha_dummy_315;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0318) 0))))
                            (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_316 f) from (by
                                unfold nb068_alpha_dummy_316;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0319 f) 0))))
                            (TAlphaVar.there
                              (show (nb068_alpha_dummy_303) ≠ (nb068_alpha_dummy_311) from (by
                                  unfold nb068_alpha_dummy_311;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0316) 0))))
                              (show (nb068_alpha_dummy_306 f) ≠ (nb068_alpha_dummy_312 f) from
                                (by
                                  unfold nb068_alpha_dummy_312;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0317 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
